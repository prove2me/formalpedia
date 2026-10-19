-- Prove2me | Theorems.Thm_HolisticService_Effort_proposition_3
-- name    : HolisticService.Effort.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:54.266519+00:00
-- url     : https://prove2.me/theorems/2e0c21ec-f231-4e6b-85f4-19f494a5f9bc
-- title:
--   Proposition 3, p. 16 — comparative statics of the optimal efforts: complementary iff same step types and [P⁻¹]ᵢⱼ > 0 or different types and [P⁻¹]ᵢⱼ < 0
-- statement:
--   Assume the standing assumptions of the service design model, no technical coupling ($\beta_{j,i} = 0$ for $j \ne i$, the paper's simplification for §4) and the interior condition $V^H_k - V^L_k \in (\underline{\Delta V}_k, \overline{\Delta V}_k)$ for every step $k$. Let $\delta^*$ be the optimal effort of the §3.3 design problem, viewed as a function of one characteristic of step $i$ at a time ($c_i$; $V^H_i$ with $V^L_i$ fixed; $\sigma^H_i$ with $\sigma^L_i$ fixed). Then, at the given parameters:
--
--   1. **Own step.** $\partial\delta^*_i/\partial c_i < 0$, $\partial\delta^*_i/\partial V^H_i > 0$, and $\partial\delta^*_i/\partial\sigma^H_i > 0$ when $\sigma^H_i - \sigma^L_i < 0$, $\partial\delta^*_i/\partial\sigma^H_i < 0$ when $\sigma^H_i - \sigma^L_i > 0$.
--
--   2. **Other steps.** For every step $j \ne i$, the four statements
--   $$\frac{\partial\delta^*_j}{\partial c_i} < 0,\quad \frac{\partial\delta^*_j}{\partial V^H_i} > 0,\quad \frac{\partial\delta^*_j}{\partial\sigma^H_i} > 0 \text{ if } \sigma^H_i-\sigma^L_i<0,\quad \frac{\partial\delta^*_j}{\partial\sigma^H_i} < 0 \text{ if } \sigma^H_i-\sigma^L_i>0$$
--   hold together if and only if
--   $$\Big(\operatorname{sgn}[\sigma^H_i-\sigma^L_i] = \operatorname{sgn}[\sigma^H_j-\sigma^L_j] \text{ and } [\mathbf P^{-1}]_{i,j} > 0\Big) \text{ or } \Big(\operatorname{sgn}[\sigma^H_i-\sigma^L_i] \ne \operatorname{sgn}[\sigma^H_j-\sigma^L_j] \text{ and } [\mathbf P^{-1}]_{i,j} < 0\Big).$$
--
--   3. **Otherwise.** If this condition fails and $[\mathbf P^{-1}]_{i,j} \ne 0$, then $\partial\delta^*_j/\partial c_i > 0$, $\partial\delta^*_j/\partial V^H_i < 0$, and $\partial\delta^*_j/\partial\sigma^H_i < 0$ when $\sigma^H_i - \sigma^L_i < 0$, $\partial\delta^*_j/\partial\sigma^H_i > 0$ when $\sigma^H_i - \sigma^L_i > 0$.
--
--   The effort at step $j$ responds to step $i$'s characteristics in the same direction as the effort at step $i$ (the efforts are complementary) exactly when the step types and the entry $[\mathbf P^{-1}]_{i,j}$ of the inverse correlation matrix agree in the sense above, and in the opposite direction (substitutable) otherwise.
--
--   **Formalization Note** $\delta^*$ is the optimizer of the design problem, chosen when one exists; it is not defined as the closed form of Proposition 1. Each derivative is the ordinary derivative along one parameter at the given point; a strict sign of a derivative also asserts differentiability. The printed "Otherwise" is restricted to $[\mathbf P^{-1}]_{i,j} \ne 0$: when $[\mathbf P^{-1}]_{i,j} = 0$ every cross derivative is $0$ and the printed claim is false, while the "iff" of item 2 holds as printed (both sides are false). $\operatorname{sgn}$ is `SignType.sign`.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 16 (PDF 16), Proposition 3 (convention Σ_{j≠i} β_{i,j} → 0 of p. 14)

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proposition 3, p. 16: the characteristics of step `i` move `δ*_i` with fixed signs, and move
`δ*_j` (`j ≠ i`) in the same direction iff `sgn[σ^H_i − σ^L_i] = sgn[σ^H_j − σ^L_j]` and `[P⁻¹]_{i,j} > 0`,
or `sgn[σ^H_i − σ^L_i] ≠ sgn[σ^H_j − σ^L_j]` and `[P⁻¹]_{i,j} < 0`; otherwise (and `[P⁻¹]_{i,j} ≠ 0`) in the
opposite direction. `δ*` is `optEffort`, the optimal effort of the §3.3 design problem. -/
theorem proposition_3 {n : ℕ} (M : Params n) (hS : M.Standing) (hβ : NoTechCoupling M)
    (hI : Interior M) (i : Fin n) :
    (deriv (fun t => optEffort (withC M i t) i) (M.c i) < 0 ∧
      0 < deriv (fun t => optEffort (withVH M i t) i) (M.VH i) ∧
      (M.sH i - M.sL i < 0 → 0 < deriv (fun t => optEffort (withSH M i t) i) (M.sH i)) ∧
      (0 < M.sH i - M.sL i → deriv (fun t => optEffort (withSH M i t) i) (M.sH i) < 0)) ∧
    ∀ j : Fin n, j ≠ i →
      let Cross :=
        deriv (fun t => optEffort (withC M i t) j) (M.c i) < 0 ∧
        0 < deriv (fun t => optEffort (withVH M i t) j) (M.VH i) ∧
        (M.sH i - M.sL i < 0 → 0 < deriv (fun t => optEffort (withSH M i t) j) (M.sH i)) ∧
        (0 < M.sH i - M.sL i → deriv (fun t => optEffort (withSH M i t) j) (M.sH i) < 0)
      let Rev :=
        0 < deriv (fun t => optEffort (withC M i t) j) (M.c i) ∧
        deriv (fun t => optEffort (withVH M i t) j) (M.VH i) < 0 ∧
        (M.sH i - M.sL i < 0 → deriv (fun t => optEffort (withSH M i t) j) (M.sH i) < 0) ∧
        (0 < M.sH i - M.sL i → 0 < deriv (fun t => optEffort (withSH M i t) j) (M.sH i))
      let Cond :=
        (SignType.sign (M.sH i - M.sL i) = SignType.sign (M.sH j - M.sL j) ∧ 0 < M.P⁻¹ i j) ∨
        (SignType.sign (M.sH i - M.sL i) ≠ SignType.sign (M.sH j - M.sL j) ∧ M.P⁻¹ i j < 0)
      (Cross ↔ Cond) ∧ (¬ Cond → M.P⁻¹ i j ≠ 0 → Rev) := by sorry

end HolisticService.Effort
