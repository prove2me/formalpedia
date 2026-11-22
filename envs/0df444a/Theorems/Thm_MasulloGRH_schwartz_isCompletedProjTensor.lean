-- Prove2me | Theorems.Thm_MasulloGRH_schwartz_isCompletedProjTensor
-- name    : MasulloGRH.schwartz_isCompletedProjTensor
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:39.664158+00:00
-- url     : https://prove2.me/theorems/0e1d9bc0-7d44-49cf-af6f-457d29c9d836
-- title:
--   Kernel theorem for Schwartz spaces: $\mathcal S(\mathbb R^m)\widehat\otimes_\pi\mathcal S(\mathbb R^n)\simeq\mathcal S(\mathbb R^m\times\mathbb R^n)$
-- statement:
--   **Schwartz kernel theorem in tensor product form for Euclidean spaces.**
--
--   For $m\ge 0$ let $\mathcal S(\mathbb R^m)$ be the Schwartz space of rapidly decreasing smooth functions $\mathbb R^m\to\mathbb C$ with its usual Fréchet topology. For locally convex spaces $E$, $F$, the projective topology $\pi$ on $E\otimes F$ is the finest locally convex topology making $\otimes:E\times F\to E\otimes F$ continuous, and $E\widehat\otimes_\pi F$ denotes the completion of $E\otimes_\pi F$.
--
--   Let $m,n\ge 0$. There is a (unique) linear map
--   $$j:\mathcal S(\mathbb R^m)\otimes\mathcal S(\mathbb R^n)\longrightarrow\mathcal S(\mathbb R^m\times\mathbb R^n),\qquad j(f\otimes g)(x,y)=f(x)\,g(y),$$
--   and it extends to a linear topological isomorphism
--   $$\mathcal S(\mathbb R^m)\,\widehat\otimes_\pi\,\mathcal S(\mathbb R^n)\ \xrightarrow{\ \sim\ }\ \mathcal S(\mathbb R^m\times\mathbb R^n).$$
--   Equivalently: $\mathcal S(\mathbb R^m\times\mathbb R^n)$ is complete, $j$ is injective, the projective topology of $\mathcal S(\mathbb R^m)\otimes\mathcal S(\mathbb R^n)$ is the topology induced by $j$ from $\mathcal S(\mathbb R^m\times\mathbb R^n)$, and the finite sums of products $f(x)g(y)$ are dense in $\mathcal S(\mathbb R^m\times\mathbb R^n)$.
--
--   This is the prototype of the "kernel theorems" of the paper (function spaces on a product are completed tensor products of the function spaces on the factors); since Schwartz spaces are nuclear, $\widehat\otimes_\pi$ may be replaced by $\widehat\otimes_\varepsilon$. The paper states analogous kernel theorems for Schwartz–Bruhat spaces of locally compact abelian groups (Theorem C.2.4.19 and Appendix D).
--
--   **Formalization Note.** $\mathcal S(\mathbb R^m)$ is Mathlib's `SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ`, and $\mathbb R^m\times\mathbb R^n$ is the product normed space `EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)`. The isomorphism of the completion with $\mathcal S(\mathbb R^m\times\mathbb R^n)$ is expressed by `IsCompletedProjTensor _ _ j` (definition file `Def_TopologicalTensorProduct_Completion`): the target is a complete Hausdorff locally convex space and $j$ is a linear topological embedding of the projective tensor product with dense range. The existence of $j$ is part of the statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 675 (end of §C.2.2.3) and p. 691 (before Theorem C.2.4.19); classical reference: F. Trèves, Topological Vector Spaces, Distributions and Kernels, Thm. 51.6

import Definitions.Def_TopologicalTensorProduct_Completion

open TensorProduct Topology Filter
open scoped SchwartzMap
set_option autoImplicit false

namespace MasulloGRH

theorem schwartz_isCompletedProjTensor (m n : ℕ) :
    ∃ j : 𝓢(EuclideanSpace ℝ (Fin m), ℂ) ⊗[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ]
        𝓢(EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n), ℂ),
      (∀ (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
          (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
          j (f ⊗ₜ[ℂ] g) p = f p.1 * g p.2) ∧
        IsCompletedProjTensor 𝓢(EuclideanSpace ℝ (Fin m), ℂ) 𝓢(EuclideanSpace ℝ (Fin n), ℂ) j := by
  sorry

end MasulloGRH
