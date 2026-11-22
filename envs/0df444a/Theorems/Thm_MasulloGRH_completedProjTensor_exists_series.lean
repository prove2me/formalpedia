-- Prove2me | Theorems.Thm_MasulloGRH_completedProjTensor_exists_series
-- name    : MasulloGRH.completedProjTensor_exists_series
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:36.938819+00:00
-- url     : https://prove2.me/theorems/e03329bb-1be3-42ac-b555-efbc3eac471d
-- title:
--   Grothendieck: every element of $E\widehat\otimes_\pi F$ ($E,F$ Fréchet) is a series $\sum_k\lambda_k\,x_k\otimes y_k$ with $(\lambda_k)\in\ell^1$, $x_k\to0$, $y_k\to0$
-- statement:
--   **Grothendieck's series representation in completed projective tensor products of Fréchet spaces.**
--
--   All vector spaces are over $\mathbb C$. For locally convex spaces $E$, $F$, the projective topology $\pi$ on $E\otimes F$ is the finest locally convex topology making $\otimes:E\times F\to E\otimes F$ continuous, and the **completed projective tensor product** $E\widehat\otimes_\pi F$ is the completion of $E\otimes_\pi F$.
--
--   Let $E$, $F$ be Fréchet spaces. Then every element $z\in E\widehat\otimes_\pi F$ can be written as
--   $$z=\sum_{k\ge 0}\lambda_k\,x_k\otimes y_k,$$
--   where $(\lambda_k)$ is an absolutely summable sequence of complex numbers and $(x_k)$, $(y_k)$ are sequences in $E$ and $F$ converging to $0$. The series converges in $E\widehat\otimes_\pi F$ (absolutely, hence unconditionally).
--
--   This result of Grothendieck reduces computations in $E\widehat\otimes_\pi F$ to elementary tensors; the paper records it as a tool for the calculations of Appendix D.
--
--   **Formalization Note.** The completed tensor product is any pair $(Y,i)$ with `IsCompletedProjTensor E F i` (definition file `Def_TopologicalTensorProduct_Completion`): $Y$ is a complete Hausdorff locally convex space and $i:E\otimes F\to Y$ is a linear topological embedding of $E\otimes_\pi F$ with dense range; all such pairs are canonically isomorphic. The conclusion is `HasSum (fun k => c k • i (x k ⊗ₜ y k)) z`, Mathlib's unconditional sum in $Y$, with `Summable (fun k => ‖c k‖)` and `Tendsto x atTop (𝓝 0)`, `Tendsto y atTop (𝓝 0)`. Sequences are indexed from $0$ (the source indexes from $1$). `IsFrechet` means locally convex, complete and metrizable.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 679, §C.2.3.2, (C.2.3.16); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, 6.4 (the result is due to Grothendieck)

import Definitions.Def_TopologicalTensorProduct_Completion

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem completedProjTensor_exists_series (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsFrechet E) (hF : IsFrechet F)
    (Y : Type v) [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (i : E ⊗[ℂ] F →ₗ[ℂ] Y) (hi : IsCompletedProjTensor E F i) (z : Y) :
    ∃ (c : ℕ → ℂ) (x : ℕ → E) (y : ℕ → F), Summable (fun k => ‖c k‖) ∧
      Tendsto x atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
      HasSum (fun k => c k • i (x k ⊗ₜ[ℂ] y k)) z := by sorry

end MasulloGRH
