-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_h10_l2_dense_embeddings
-- name    : HunterPDE.Parabolic.h10_l2_dense_embeddings
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-17T04:51:15.151172+00:00
-- url     : https://prove2.me/theorems/b9aa4ac5-ee6b-4574-8add-eecc0e7c44c9
-- title:
--   For open $\Omega$ the embeddings $H^1_0(\Omega)\hookrightarrow L^2(\Omega)\hookrightarrow H^{-1}(\Omega)$ are injective with dense range
-- statement:
--   Let $\Omega\subset\mathbb{R}^n$ be open. The inclusion $\iota: H^1_0(\Omega)\to L^2(\Omega)$, $u\mapsto u$, and the map $J: L^2(\Omega)\to H^{-1}(\Omega)$, $J f = (f,\cdot)_{L^2}\big|_{H^1_0(\Omega)}$, i.e.
--   $$\langle Jf, v\rangle = \int_\Omega f\,v\,dx \qquad (v\in H^1_0(\Omega)),$$
--   are both injective with dense range. Together with separability this makes $H^1_0(\Omega)\subset L^2(\Omega)\subset H^{-1}(\Omega)$ a Hilbert triple in the sense of Definition 6.40.
--
--   Role: this is the Hilbert triple to which Theorems 6.41 and 6.42 are applied in the proof of Proposition 6.7 (continuity in time of the limit and the identification of its initial value), and injectivity of $\iota$ is used to pass from the weak equation on a dense set of test functions to all of $H^1_0(\Omega)$.
--
--   **Formalization Note**: $H^1_0(\Omega)$ is the published closure of the jets of $C_c^\infty(\Omega)$ in $L^2(\Omega;\mathbb{R}\times\mathbb{R}^n)$ and $\iota$ is the published `toL2L` (first component of the jet); $J f$ is written as `(innerSL ℝ f).comp (toL2L n Ω)`, an element of $H^{-1}(\Omega)=$ `StrongDual ℝ (H10 n Ω)`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, p. 207, Definition 6.40 and the Hilbert triple H^1_0(Ω) ⊂ L^2(Ω) ⊂ H^{-1}(Ω) used in §6.1 (proof of Proposition 6.7, p. 186)

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10

namespace HunterPDE.Parabolic

open MeasureTheory

theorem h10_l2_dense_embeddings {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) :
    Function.Injective (toL2L n Ω) ∧ DenseRange (toL2L n Ω) ∧
      Function.Injective (fun f : Lp ℝ 2 (volume.restrict Ω) => (innerSL ℝ f).comp (toL2L n Ω)) ∧
      DenseRange (fun f : Lp ℝ 2 (volume.restrict Ω) => (innerSL ℝ f).comp (toL2L n Ω)) := by sorry

end HunterPDE.Parabolic
