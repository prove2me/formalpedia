-- Prove2me | Theorems.Thm_GaussDiffSVP_theorem_5_2
-- name    : GaussDiffSVP.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:04:24.305683+00:00
-- url     : https://prove2.me/theorems/ae5a664d-028d-46f3-9539-f3cd34ee2e8c
-- title:
--   Theorem 5.2 — Gaussian cooling: root in $\mathcal C(\nu_{p,r_0,\Upsilon_0},e^{-\Omega(nw_n^2)})$, $\Upsilon_0 = 2^{\varrho n+\Theta(b_n)}$
-- statement:
--   Choose $u = u_n$ from (39), a bounded raw sampling rate $\varrho_n\ge P(u)+J(a_0)$ and a depth $t_n$ with $\gamma^2\le1-w_n/4$ and $t(h_n+\ell_n) = o(b_n)$, for either schedule (163) or (166); then also $t = o(nw_n^2)$ and $nw_n^2 = o(h_n)$. Fix $\Gamma$, $s$ with $\epsilon_\Gamma\le2^{-h_n/3}$, $C_a>0$ and the external offsets, and build the ideal isolated tree (Algorithm 1) at starting width $R = r_0\gamma^{-t}$ satisfying Lemma 3.3, with leaf pools of $2M_{\mathrm{leaf}}$ corrected trials,
--   $$M_{\mathrm{leaf}} = \lceil2^{\varrho n+C_ab_n}\rceil,\qquad\Upsilon_t = M_{\mathrm{leaf}},\ \Upsilon_{j-1} = \Upsilon_j2^{-h_n-b_{\deg}},$$
--   and activation probabilities (45). For all sufficiently large $n$:
--
--   1. all pair probabilities are at most one;
--   2. every root satisfies $\Xi_0\in\mathcal C(\nu_{p,r_0,\Upsilon_0},\varepsilon_0)$ with $\varepsilon_0\le e^{-\Omega(nw_n^2)}$;
--   3. $\Upsilon_0 = 2^{\varrho n+\sigma_0}$ with $\sigma_0 = C_ab_n-\sum_{j=1}^t(h_n+b_{\deg})+O(1) = \Theta(b_n)$;
--   4. the expected list size is $2^{[\varrho-J(a_0)]n+\Theta(b_n)}$.
--
--   Independently constructed roots are independent conditional on their common public parameters and external offsets. The cooled roots are the Gaussian input lists of the full difference trees of Section 8.
--
--   Differences from the source:
--   - encoding: conditions on the sequences $u_n,\varrho_n$ → required eventually in $n$; reason: at $n=0$, $w_0 = 1$ makes $\gamma^2\le1-w_0/4$ incompatible with $u\le31/50$
--   - reading: bounded $\varrho_n$ → $\varrho_n\le M$ for one $M$; reason: $\varrho_n\ge P+J>0$
--   - reading: $\Omega$, $O(1)$, $\Theta$, sufficiently large $n$ → constants and $n_0$ fixed after the sequences and $C_a$, before $\Gamma$, $s$, $p$ and the coins; reason: uniformity as stated
--   - reading: starting width satisfying Lemma 3.3 → $R\ge\|b_i^*\|\sqrt{\log(8n)/\pi}$ for every Gram–Schmidt vector of the basis $B$; reason: Lemma 3.3's hypothesis
--   - encoding: the ideal forest with pairwise independent coins → `buildIdealLaw` for every coin kernel family with the marginals (45); reason: Algorithm 1 does not fix the coin family
--   - encoding: independently constructed roots are conditionally independent → not a separate conjunct; reason: each root law is given the public parameters and its offset; independent roots are drawn from the product law by construction
--   - encoding: $\Upsilon_j$ → $M_{\mathrm{leaf}}2^{-(t-j)(h_n+b_{\deg})}$; reason: the recursion $\Upsilon_{j-1} = \Upsilon_j2^{-h_n-b_{\deg}}$ solved
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 5.2, p.30; (48), Algorithm 1, p.29

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_GaussDiffSVP_AdmissibleBudget
import Definitions.Def_GaussDiffSVP_rateJ
import Definitions.Def_GaussDiffSVP_rateP
import Definitions.Def_GaussDiffSVP_InClassC
import Definitions.Def_GaussDiffSVP_IsCoinKernel
import Definitions.Def_GaussDiffSVP_coolKernel
import Definitions.Def_GaussDiffSVP_gaussRef
import Definitions.Def_GaussDiffSVP_buildIdealLaw

open Filter Topology SuperlatSVP
open scoped ENNReal

namespace GaussDiffSVP

/-- Theorem 5.2 (Gaussian cooling) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.30), for either schedule of Appendices C.1.2 and C.3.2.

*Parameters.* `u = u_n ∈ (1/2, 31/50]` from (39) (`a₀ = 1/(1 + u)`, `γ² = 2(1 − u)`), a bounded raw
sampling rate `ϱ_n ≥ P(u₁) + J(a₀)`, and a depth `t_n` with `γ² ≤ 1 − w_n/4` and
`t(h_n + ℓ_n) = o(b_n)`. Then also `t = o(n w_n²)` and `n w_n² = o(h_n)`.

*Construction.* `Γ = Bℤⁿ`, `s` with `ϵ_Γ ≤ 2^{−h_n/3}`, `r₀ = √2 s`, `r_j = r₀γ^{−j}`, `C_a > 0`, external
offset `p`; the ideal isolated tree (Algorithm 1) at starting width `R = r₀γ^{−t}` satisfying
Lemma 3.3 (`R ≥ G√(log(8n)/π)`, `G = max_i ‖b_i^*‖`), with leaf pools of `2M_leaf` corrected trials,
`M_leaf = ⌈2^{ϱn + C_a b_n}⌉` (48), coefficients `Υ_t = M_leaf`, `Υ_{j−1} = Υ_j 2^{−h_n − b_deg}`,
`b_deg = ⌈10ℓ_n⌉`, and activation probabilities (45) (`coolKernel`) realized by pairwise independent
coins.

*Root guarantee.* For all sufficiently large `n`:
1. all pair probabilities are at most one;
2. every root satisfies `Ξ₀ ∈ C(ν_{p,r₀,Υ₀}, ε₀)` with `ε₀ ≤ e^{−Ω(n w_n²)}`;
3. `Υ₀ = 2^{ϱn + σ₀}` with `σ₀ = C_a b_n − ∑_{j=1}^t (h_n + b_deg) + O(1) = Θ(b_n)` (49);
4. the expected size is `2^{[ϱ − J(a₀)]n + Θ(b_n)}`.

Independently constructed roots are independent conditional on their common public parameters and
external offsets.

**Formalization Note.** Sequences are functions of `n`. Their conditions are required eventually
(`∀ᶠ n`): at `n = 0`, `w_0 = 1` makes `γ² ≤ 1 − w_0/4` incompatible with `u ≤ 31/50`. "Bounded" is
`ϱ_n ≤ M`. The asymptotic constants (`Ω`, `O(1)`, `Θ`) and `n₀` are fixed after the sequences and
`C_a`, before `B`, `s`, `p` and the coin kernels. The root law is `buildIdealLaw`, indexed by an
arbitrary pairwise-independent coin kernel family with the marginals (45) at every level. The
conditional-independence clause holds by construction: each root's law is a law given the public
parameters and its offset, and independently constructed roots are drawn from the product of these
laws, so it is not a separate conjunct. -/
theorem theorem_5_2 (β : Budget) (hβ : AdmissibleBudget β) (u ϱ : ℕ → ℝ) (t : ℕ → ℕ)
    (Ca : ℝ) (hCa : 0 < Ca)
    (hu : ∀ᶠ n in atTop, 1 / 2 < u n ∧ u n ≤ 31 / 50 ∧ 2 * (1 - u n) ≤ 1 - β.w n / 4)
    (hϱM : ∃ M : ℝ, ∀ n, ϱ n ≤ M)
    (hϱ : ∀ᶠ n in atTop, rateP (u n) + rateJ (1 / (1 + u n)) ≤ ϱ n)
    (ht : Tendsto (fun n => (t n : ℝ) * (β.h n + β.ell n) / β.b n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (t n : ℝ) / (n * β.w n ^ 2)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * β.w n ^ 2 / β.h n) atTop (𝓝 0) ∧
    ∃ c C c₁ c₂ c₃ c₄ : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 0 < c₁ ∧ 0 < c₃ ∧ ∀ n : ℕ, n₀ ≤ n →
      let w := β.w n
      let h := β.h n
      let ℓ := β.ell n
      let bdeg : ℕ := ⌈10 * ℓ⌉₊
      let γ := Real.sqrt (2 * (1 - u n))
      let M : ℕ := ⌈(2 : ℝ) ^ (ϱ n * n + Ca * β.b n)⌉₊
      let Υ : ℕ → ℝ := fun j => M * (2 : ℝ) ^ (-(((t n : ℝ) - j) * (h + bdeg)))
      let σ₀ := Real.logb 2 (Υ 0) - ϱ n * n
      (|σ₀ - (Ca * β.b n - ∑ j ∈ Finset.Icc 1 (t n), (h + bdeg))| ≤ C ∧
        c₁ * β.b n ≤ σ₀ ∧ σ₀ ≤ c₂ * β.b n) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → ∀ s : ℝ, 0 < s →
        rhoSet (1 / s) {y | y ∈ RegevLWE.GaussConv.dual (lat B) ∧ y ≠ 0} ≤
          ENNReal.ofReal ((2 : ℝ) ^ (-(h / 3))) →
        (∀ i : Fin n, ‖InnerProductSpace.gramSchmidt ℝ (fun k : Fin n => vecE (fun l => B l k)) i‖ *
            Real.sqrt (Real.log (8 * n) / Real.pi) ≤ Real.sqrt 2 * s / γ ^ (t n)) →
        (∀ j : ℕ, 1 ≤ j → j ≤ t n → ∀ x y : E n,
          coolKernel w h ℓ (u n) (Real.sqrt 2 * s / γ ^ j) (Υ j) x y ≤ 1) ∧
        ∀ κ : ℕ → E n → (Fin n → ZMod 2) → (lL : List (E n)) → (lR : List (E n)) →
            PMF (Fin lL.length × Fin lR.length → Bool),
          (∀ j : ℕ, 1 ≤ j → j ≤ t n → ∀ q e,
            IsCoinKernel (coolKernel w h ℓ (u n) (Real.sqrt 2 * s / γ ^ j) (Υ j)) (κ j q e)) →
          ∀ p : E n,
            InClassC (buildIdealLaw B w (u n) s (t n) M κ p)
                (gaussRef B (Real.sqrt 2 * s) w (1 / (1 + u n)) (Υ 0) p)
                (Real.exp (-(c * n * w ^ 2))) ∧
            ENNReal.ofReal ((2 : ℝ) ^ ((ϱ n - rateJ (1 / (1 + u n))) * n + c₃ * β.b n)) ≤
              ∑' x : E n, intensity (buildIdealLaw B w (u n) s (t n) M κ p) x ∧
            ∑' x : E n, intensity (buildIdealLaw B w (u n) s (t n) M κ p) x ≤
              ENNReal.ofReal ((2 : ℝ) ^ ((ϱ n - rateJ (1 / (1 + u n))) * n + c₄ * β.b n)) := by sorry

end GaussDiffSVP
