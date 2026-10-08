-- Prove2me | Theorems.Thm_MPECRelax_KDBConv_multipliers_bounded
-- name    : MPECRelax.KDBConv.multipliers_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:08.699779+00:00
-- url     : https://prove2.me/theorems/4ed5e74b-4ef8-4b11-bba2-163af716c5a2
-- title:
--   Proof of Theorem 3.5, p. 16 — under MPEC-CPLD the multiplier sequence is bounded
-- statement:
--   Let the data of the MPEC (1) be continuously differentiable, let $x^k\to x^*$, and let MPEC-CPLD hold at $x^*$. Let $\lambda^k\in\mathbb R^m$, $\mu^k\in\mathbb R^p$, $\alpha^k,\beta^k,\eta^{G,k},\eta^{H,k}\in\mathbb R^l$ be sequences of coefficients with $\lambda^k\ge 0$ such that, for every $k$,
--
--   1. (11) holds at $x^k$:
--   $$0=\nabla f(x^k)+\sum_i\lambda^k_i\nabla g_i(x^k)+\sum_j\mu^k_j\nabla h_j(x^k)-\sum_i(\alpha^k_i+\eta^{G,k}_i)\nabla G_i(x^k)-\sum_i(\beta^k_i+\eta^{H,k}_i)\nabla H_i(x^k);$$
--   2. the disjointness relations (13) hold;
--   3. the gradients (15) at $x^k$, extended by $\nabla g_i(x^k)$ ($i\in\operatorname{supp}\lambda^k$) and $\nabla h_j(x^k)$ ($j\in\operatorname{supp}\mu^k$), are linearly independent;
--
--   and, for all $k$ sufficiently large, the support inclusions (12) hold: $\operatorname{supp}(\lambda^k)\subseteq I_g$, $\operatorname{supp}(\alpha^k),\operatorname{supp}(\eta^{G,k})\subseteq I_{00}\cup I_{0+}$, $\operatorname{supp}(\beta^k),\operatorname{supp}(\eta^{H,k})\subseteq I_{00}\cup I_{+0}$ (index sets at $x^*$). Then the sequence
--   $$\{(\lambda^k,\mu^k,\alpha^k,\beta^k,\eta^{G,k},\eta^{H,k})\}$$
--   is bounded.
--
--   This is the step where MPEC-CPLD enters: it yields convergent subsequences of the multipliers, whose limits become the MPEC multipliers of $x^*$.
--
--   **Formalization Note** The paper states boundedness of $\{(\alpha^k,\beta^k,\eta^{G,k},\eta^{H,k})\}$ with the standard constraints skipped; here the standard-constraint multipliers $\lambda^k,\mu^k$ are included, and the hypotheses are the properties the proof has established at that point (with (15) extended by the standard-constraint gradients). Boundedness is stated as a uniform bound $C$ on the sup norms of all six components.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 16, proof of Theorem 3.5, boundedness of {(α^k, β^k, η^{G,k}, η^{H,k})}

import Mathlib
import Definitions.Def_MPECRelax_KDBConv_Basic

open Filter Topology

namespace MPECRelax.KDBConv

/-- Proof of Theorem 3.5, p. 16: boundedness of the multiplier sequence. Let the data be
C¹, `x^k → xs`, and MPEC-CPLD hold at `xs`. Let coefficient sequences `λ^k ≥ 0`, `µ^k`,
`α^k`, `β^k`, `η^{G,k}`, `η^{H,k}` satisfy, for every `k`, (11) at `x^k` (standard
constraints kept), (13), and the linear independence (15) at `x^k` extended by the
standard-constraint gradients, and, for all `k` sufficiently large, the support inclusions
(12) together with `supp(λ^k) ⊆ I_g`. Then the sequence
`(λ^k, µ^k, α^k, β^k, η^{G,k}, η^{H,k})` is bounded (in the sup norm). -/
theorem multipliers_bounded {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (x : ℕ → MPECRelax.ScholtesConv.E n) (xs : MPECRelax.ScholtesConv.E n) (hx : Tendsto x atTop (𝓝 xs)) (hCQ : P.MPEC_CPLD xs)
    (lam : ℕ → Fin m → ℝ) (mu : ℕ → Fin p → ℝ) (α β ηG ηH : ℕ → Fin l → ℝ)
    (h11 : ∀ k, gradient P.f (x k) + ∑ i, lam k i • gradient (P.g i) (x k)
        + ∑ j, mu k j • gradient (P.h j) (x k)
        - ∑ i, α k i • gradient (P.G i) (x k) - ∑ i, β k i • gradient (P.H i) (x k)
        - ∑ i, ηG k i • gradient (P.G i) (x k) - ∑ i, ηH k i • gradient (P.H i) (x k) = 0)
    (hlam : ∀ k i, 0 ≤ lam k i)
    (h12 : ∀ᶠ k in atTop, Function.support (lam k) ⊆ P.Ig xs ∧
      Function.support (α k) ⊆ P.I00 xs ∪ P.I0p xs ∧
      Function.support (β k) ⊆ P.I00 xs ∪ P.Ip0 xs ∧
      Function.support (ηG k) ⊆ P.I00 xs ∪ P.I0p xs ∧
      Function.support (ηH k) ⊆ P.I00 xs ∪ P.Ip0 xs)
    (h13 : ∀ k, Function.support (α k) ∩ Function.support (ηG k) = ∅ ∧
      Function.support (β k) ∩ Function.support (ηH k) = ∅ ∧
      Function.support (ηG k) ∩ Function.support (ηH k) = ∅)
    (h15 : ∀ k, LinearIndependent ℝ
        (Sum.elim (fun i : ↥(Function.support (lam k)) => gradient (P.g i.1) (x k))
          (Sum.elim (fun j : ↥(Function.support (mu k)) => gradient (P.h j.1) (x k))
            (Sum.elim
              (fun i : ↥(Function.support (α k) ∪ Function.support (ηG k)) =>
                gradient (P.G i.1) (x k))
              (fun i : ↥(Function.support (β k) ∪ Function.support (ηH k)) =>
                gradient (P.H i.1) (x k)))))) :
    ∃ C : ℝ, ∀ k, ‖lam k‖ ≤ C ∧ ‖mu k‖ ≤ C ∧ ‖α k‖ ≤ C ∧ ‖β k‖ ≤ C ∧
      ‖ηG k‖ ≤ C ∧ ‖ηH k‖ ≤ C := by sorry

end MPECRelax.KDBConv
