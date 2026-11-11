-- Prove2me | Theorems.Thm_LindbladShallow_theorem_3_7
-- name    : LindbladShallow.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:22:58.290044+00:00
-- url     : https://prove2.me/theorems/49a0fea7-5546-4491-ac6e-add5db170cd3
-- title:
--   Theorem 3.7 — occupation bounds for local simulation inputs
-- statement:
--   For a valid input with $N_0,\tau,R$ of Eq. (11), any number of periods $M\ge1$ and windows $r\ge1$ with $r\mid M$ ($h=\tau/M$), and the exact local factors executed in colour and owner order as window calls $W_C=V^{(c)}_{C,r}\cdots V^{(c)}_{C,1}V^{(c-1)\dagger}_{C,1}\cdots V^{(c-1)\dagger}_{C,r}$ (old inverse windows first): for every call, let $Y_{\mathrm{in}}$ be the ideal global prefix isometry before it. For a forward window $V=V_L\cdots V_1$ consider $Y_{\mathrm{in}}$ and the columns $V_{<j}Y_{\mathrm{in}}$; for an inverse window $V^\dagger$ consider $V^\dagger Y_{\mathrm{in}}$ and $V_{<j}V^\dagger Y_{\mathrm{in}}$ ($V_{<1}=I$). Then there are nonnegative $a_b$, common to the whole call family, satisfying Eqs. (12)–(14) of Lemma 3.6 on the complete local bath set $\mathcal B_{\mathrm{cat}}(C)$ for every one of these columns, and
--   $$\sum_{b\in\mathcal B_{\mathrm{cat}}}a_b^2\le\frac{\nu\Sigma_*}4,\qquad \nu=2\cdot7^D+4,\quad \Sigma_*=\nu\lambda\tau v_*,\quad v_*=(9R)^D.$$
--   The bounds include occupied spectators and are independent of the numbers of windows and periods.
--
--   This supplies the occupation control under which each local factor can be simulated by the transducer construction (Theorem 5.1).
--
--   Differences from the source:
--   - generalization: windows and periods of Eq. (15) → every M ≥ 1 and r ≥ 1 with r ∣ M (h = τ/M); reason: the bound is independent of the numbers of windows and periods; Eq. (15)'s choice has r ∣ M
--   - generalization: the prescribed owner order → every order of the owners within a colour; reason: the visit counts and weights do not depend on it; the source's order is one of them
--   - reading: all columns required by the forward analysis → the prefixes V_{<j} for 1 ≤ j ≤ L (only the identity prefix for an empty window), applied to Y_in or V†Y_in; reason: these are the columns named on p.20
--   - encoding: the complete localized product and its window calls → a list of calls (owner, forward window word, inverse flag) in colour then owner order, the prefix isometry being the product of earlier calls applied to E₀; reason: same circuit
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Theorem 3.7, p.21; windows Eqs. (15)–(16), p.20; B_cat p.19

import Mathlib
import Definitions.Def_LindbladShallow_localDecomp

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- **Theorem 3.7** (Occupation bounds for local simulation inputs; arXiv:2610.05362, held version
sha256 8f4637ef…, p.21, with the windows of Eqs. (15)–(16), p.20). The exact local factors follow
their colour and owner order, each factor `W_C = V^{(c)}_{C,r} ⋯ V^{(c)}_{C,1} V^{(c−1)†}_{C,1} ⋯
V^{(c−1)†}_{C,r}` executed as window calls (old inverse windows first). For a forward window
`V = V_L ⋯ V_1` with ideal input `Y_in` (the global prefix isometry before the call) consider `Y_in`
and all columns `V_{<j}Y_in`; for an inverse window `V†` consider `V†Y_in` and all columns
`V_{<j}V†Y_in` (`V_{<1} = I`; an empty window has only the identity prefix). Each call family
satisfies Lemma 3.6 (Eqs. (12)–(14)) on the complete local bath set `B_cat` of `C` with one common
set of nonnegative bounds `a_b` and `Σ_b a_b² ≤ νΣ∗/4`, where `ν := 2·7^D + 4`,
`Σ∗ := νλτv∗`, `v∗ = (9R)^D`. The bounds are independent of the numbers of windows and periods.

**Formalization Note** `N₀, τ, R` are those of Eq. (11); the statement holds for every number of
periods `M ≥ 1` and windows `r ≥ 1` with `r ∣ M` (`h = τ/M`), which covers Eq. (15)'s choice. The
owners of one colour are taken in an arbitrary order `ord`. `B_cat` contains spectator baths
(all periods, all owners within ℓ∞ distance 3). -/
theorem theorem_3_7 {P : Params} (I : Instance P) (hI : I.Valid) (M r : ℕ) (hM : 1 ≤ M)
    (hr : 1 ≤ r) (hrM : r ∣ M) (ord : List (Fin P.D → ℤ)) (hord : ord.Nodup)
    (hordC : ∀ C, C ∈ ord ↔ C ∈ CLam I (Rlen I)) :
    let R := Rlen I
    let h := tau I / M
    let ν : ℝ := 2 * 7 ^ P.D + 4
    let Sig : ℝ := ν * lam I * tau I * (9 * (R : ℝ)) ^ P.D
    ∀ (k : ℕ) (hk : k < (callList I M R r ord).length),
      let x := (callList I M R r ord).get ⟨k, hk⟩
      let Yin := prefixY I M R r h ord k
      ∃ a : BJ I M → ℝ, (∀ b, 0 ≤ a b) ∧
        ∑ b ∈ Bcat I M R x.1, a b ^ 2 ≤ ν * Sig / 4 ∧
        ∀ j < max x.2.1.length 1,
          OccBounds (Bcat I M R x.1) a
            (if x.2.2 then wordU I M h (x.2.1.take j) * wordU I M h (adjWord x.2.1) * Yin
             else wordU I M h (x.2.1.take j) * Yin) := by sorry

end LindbladShallow
