-- Prove2me | Theorems.Thm_GoodViewsNotEnough_whitened_optima_retain_nuisance
-- name    : GoodViewsNotEnough.whitened_optima_retain_nuisance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:55:00.326555+00:00
-- url     : https://prove2.me/theorems/6cc93d1b-7a66-4c33-abdb-ece22dc46df1
-- title:
--   Theorem 2: all whitened soft-objective optima retain nuisance
-- statement:
--   In the 512-dimensional model, encoders $h(S,U)\in\mathbb{R}^{512}$ are constrained to be whitened: $\mathbb{E}h=0$, $\mathbb{E}hh^\top=I_{512}$. The objective is
--
--   $$F(h)=\frac54u(h)+\frac1{50}\bar R(h),\qquad u(h)=\frac1{512}\mathbb{E}\|h-\mathbb{E}[h\mid S]\|^2,$$
--
--   where $\bar R$ is the expected pooled Epps–Pulley statistic of eq. (20). Then:
--
--   1. $F$ attains its minimum over whitened encoders;
--   2. every global minimiser satisfies $u(h)>0.00015$;
--   3. for any two global minimisers $h_1,h_2$, evaluated on the same scene $S$ with independent nuisances $U_1,U_2$, and for every $Q\in O(512)$,
--   $$\frac1{512}\mathbb{E}\|h_1(S,U_1)-Qh_2(S,U_2)\|^2>0.0003.$$
--
--   The same three statements hold in the linear class $h_W(S,U)=W(r(S),U)$, $W\in\mathbb{R}^{512\times1024}$, $WW^\top=I_{512}$, where $r$ is a complete centred orthonormal scene basis. In that class, minimum and minimisers are taken over $W$.
--
--   The model has a complete scene basis, a spectral gap and exact whitening. Even so, the pooled Gaussian regulariser forces every optimum to retain nuisance, and independently trained modalities stay misaligned after the best rotation.
--
--   **Formalization Note** The paper states the alignment bound as $\min_{Q\in O(k)}(\cdots)>0.0003$. It is written here as a bound for every $Q$, which is equivalent because $O(512)$ is compact and the minimum is attained. The constants are $0.00015=3/20000$ and $0.0003=3/10000$, as in Theorem 8.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Section 5, Theorem 2, eq. (2), p. 5; restated as Theorem 8 with eqs. (17), (21), Appendix D.4, pp. 18-19

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex

namespace GoodViewsNotEnough

theorem whitened_optima_retain_nuisance (r : Fin 513 → Fin 512 → ℝ)
    (hr : IsCenteredOrthonormalBasis r) :
    (∃ h, IsWhitenedHD h ∧ IsMinOn highObjective {h | IsWhitenedHD h} h) ∧
    (∀ h, IsWhitenedHD h → IsMinOn highObjective {h | IsWhitenedHD h} h →
      3 / 20000 < nuisanceFrac h) ∧
    (∀ h₁ h₂, IsWhitenedHD h₁ → IsMinOn highObjective {h | IsWhitenedHD h} h₁ →
      IsWhitenedHD h₂ → IsMinOn highObjective {h | IsWhitenedHD h} h₂ →
      ∀ Q ∈ Matrix.orthogonalGroup (Fin 512) ℝ, 3 / 10000 < alignErr h₁ h₂ Q) ∧
    (∃ W, IsStiefel W ∧ IsMinOn (fun W => highObjective (linEncoder r W)) {W | IsStiefel W} W) ∧
    (∀ W, IsStiefel W → IsMinOn (fun W => highObjective (linEncoder r W)) {W | IsStiefel W} W →
      3 / 20000 < nuisanceFrac (linEncoder r W)) ∧
    (∀ W₁ W₂, IsStiefel W₁ →
      IsMinOn (fun W => highObjective (linEncoder r W)) {W | IsStiefel W} W₁ →
      IsStiefel W₂ → IsMinOn (fun W => highObjective (linEncoder r W)) {W | IsStiefel W} W₂ →
      ∀ Q ∈ Matrix.orthogonalGroup (Fin 512) ℝ,
        3 / 10000 < alignErr (linEncoder r W₁) (linEncoder r W₂) Q) := by sorry

end GoodViewsNotEnough
