-- Prove2me | Theorems.Thm_OpenPitMIP_Vrhs_eq_36
-- name    : OpenPitMIP.Vrhs.eq_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:09.515482+00:00
-- url     : https://prove2.me/theorems/759f6687-c2e6-4dbd-8725-acf79c54a088
-- title:
--   (36), proof of Theorem 7, p. 1435 — under (33), ∑_{b∈c_n} α_b q_b y_{b,d,t} ≤ δ_n w_{c_n,t}
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions, a destination $d$, a period $t$, and clusters $c_1\prec c_2\prec\dots\prec c_n$ ($n\ge 1$). Let $\delta_n=U^d_t-q(rcl(c_1)\setminus rcl(c_n))$, and let constants $0\le\alpha_b\le 1$ ($b\in c_n$) satisfy
--   $$\sum_{b\in c_n}\alpha_b q_b\ \le\ U^d_t-q(rcl(c_1)\setminus rcl(c_n)).\tag{33}$$
--   Then every $(x,y)$ feasible for the PCPSP-C under either integrality condition satisfies, with $w_{c,t}=\sum_{t'=1}^{t}x_{c,t'}$,
--   $$\sum_{b\in c_n}\alpha_b q_b\,y_{b,d,t}\ \le\ \delta_n\,w_{c_n,t}.\tag{36}$$
--
--   This is the estimate for the last cluster of the chain in the partial-integrality case of the proof of Theorem 7; condition (33) is what makes it hold.
--
--   **Formalization Note** The page derives (36) in the subcase "$k_o=n$ and partial integrality"; the inequality itself uses neither, nor conditions 2 and 3 of Theorem 7, so it is stated for every feasible point under both integrality conditions (a stronger statement). The page cites "(29) and (33)"; the step it uses is (30).
-- source:
--   Oper. Res. 68(5), proof of Theorem 7, (36), p. 1435

import Mathlib
import Definitions.Def_OpenPitMIP_Vrhs_Setting

namespace OpenPitMIP.Vrhs

open PCPSPC

/-- (36), proof of Theorem 7, Oper. Res. 68(5), p. 1435: along a chain `c₁ ≺ ⋯ ≺ c_n`, if
`0 ≤ α_b ≤ 1` on `c_n` and (33) `∑_{b ∈ c_n} α_b q_b ≤ U_t^d − q(rcl(c₁) \ rcl(c_n))` holds, then
every feasible `(x, y)` of the PCPSP-C (either integrality condition) satisfies
`∑_{b ∈ c_n} α_b q_b y_{b,d,t} ≤ δ_n w_{c_n,t}`. -/
theorem eq_36 {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (d : D) (t : Fin T) (n : ℕ) (hn : 1 ≤ n)
    (c : ℕ → C) (h1 : ∀ k ∈ Finset.Ico 1 n, I.cprec (c k) (c (k + 1)))
    (α : B → ℝ) (hα : ∀ b ∈ I.blocksOf {c n}, 0 ≤ α b ∧ α b ≤ 1)
    (h33 : ∑ b ∈ I.blocksOf {c n}, α b * I.q b ≤ I.Ud d t - I.qSet (I.rcl (c 1) \ I.rcl (c n)))
    (κ : OpenPitMIP.UltPit.Integrality) (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hxy : I.Feasible κ x y) :
    ∑ b ∈ I.blocksOf {c n}, α b * I.q b * y b d t ≤ I.delta d t c n n * cum x (c n) t := by sorry

end OpenPitMIP.Vrhs
