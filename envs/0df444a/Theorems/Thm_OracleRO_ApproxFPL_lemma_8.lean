-- Prove2me | Theorems.Thm_OracleRO_ApproxFPL_lemma_8
-- name    : OracleRO.ApproxFPL.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:30:53.36071+00:00
-- url     : https://prove2.me/theorems/be4f67c0-b087-4a75-8656-be99c6a6d55e
-- title:
--   Lemma 8 — be the approximate perturbed leader: $\sum_t M_\epsilon(f_{1:t}+p)\cdot f_t \ge f_{1:T}\cdot x - D/\eta - 2\epsilon T$
-- statement:
--   Let $\mathcal K \subseteq \mathbb R^n$, $\epsilon > 0$, and $M_\epsilon$ an $\epsilon$-approximate linear optimization procedure over $\mathcal K$. Let $D$ be an upper bound on the $\ell_1$ diameter of $\mathcal K$, that is $\|x-y\|_1 = \sum_i |x_i - y_i| \le D$ for all $x,y\in\mathcal K$. Let $\eta > 0$, let $T \ge 2$, let $f_1,\ldots,f_T\in\mathbb R^n$ be arbitrary, and let $p \in [0,1/\eta]^n$ be a fixed vector. Then for every $x \in \mathcal K$,
--   $$
--   \sum_{t=1}^T M_\epsilon(f_{1:t} + p) \cdot f_t \;\ge\; f_{1:T} \cdot x - \frac{D}{\eta} - 2\epsilon T .
--   $$
--
--   This is a deterministic bound on the reward of the hypothetical algorithm that uses the not-yet-observed $f_t$ together with the perturbation $p$; the perturbation costs at most $D/\eta$ in total. Combined with the stability bound (Lemma 9) it yields the regret bound of Theorem 6.
--
--   **Formalization Note** The paper writes the right side as $\max_{x\in\mathcal K} f_{1:t}\cdot x - D/\eta - 2\epsilon T$, where $t$ is not bound; it means $f_{1:T}$. The maximum is replaced by "for every $x \in \mathcal K$", which needs no attainment.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 12, Lemma 8

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_IsApproxLinOracle
import Definitions.Def_OracleRO_ApproxFPL_FPL

open MeasureTheory ProbabilityTheory

namespace OracleRO.ApproxFPL

/-- Lemma 8 (arXiv:1402.6361v1, p. 12): the hypothetical "be the perturbed leader" algorithm.
For `T ≥ 2`, a fixed perturbation `p ∈ [0, 1/η]ⁿ` and `D` an upper bound on the `ℓ₁` diameter
of `K`, for every `x ∈ K`,
`∑_{t=1}^T M(f_{1:t} + p) · f_t ≥ f_{1:T} · x - D/η - 2εT`.
(The page writes `max_{x ∈ K} f_{1:t} · x`; `t` is not bound there and means `T`.) -/
theorem lemma_8 {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M)
    (D : ℝ) (hD : ∀ x ∈ K, ∀ y ∈ K, ∑ i, |x i - y i| ≤ D)
    (η : ℝ) (hη : 0 < η) (f : ℕ → Fin n → ℝ) (T : ℕ) (hT : 2 ≤ T)
    (p : Fin n → ℝ) (hp : p ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => η⁻¹)) :
    ∀ x ∈ K, prefixSum f T ⬝ᵥ x - D / η - 2 * ε * T ≤
      ∑ t ∈ Finset.Icc 1 T, M (prefixSum f t + p) ⬝ᵥ f t := by sorry

end OracleRO.ApproxFPL
