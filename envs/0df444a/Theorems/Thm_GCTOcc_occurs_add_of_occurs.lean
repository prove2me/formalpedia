-- Prove2me | Theorems.Thm_GCTOcc_occurs_add_of_occurs
-- name    : GCTOcc.occurs_add_of_occurs
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T17:36:22.525663+00:00
-- url     : https://prove2.me/theorems/73ad0c8c-5379-4063-967e-20b2dc6e681d
-- title:
--   Lemma 2.2 — occurring partitions for $\Omega_n$ form a semigroup
-- statement:
--   If $\lambda$ occurs in the coordinate ring of $\Omega_n$ in degree $d_1$ and $\mu$ occurs in degree $d_2$, then the sum $\lambda + \mu$, taken part by part, occurs in degree $d_1 + d_2$:
--
--   $$\lambda \text{ occurs in } \mathbb{C}[\Omega_n]_{d_1}, \quad \mu \text{ occurs in } \mathbb{C}[\Omega_n]_{d_2} \;\Longrightarrow\; \lambda+\mu \text{ occurs in } \mathbb{C}[\Omega_n]_{d_1+d_2}.$$
--
--   The argument in the source is short: occurrence means the existence of a highest weight vector of the given weight in the coordinate ring, the product of highest weight vectors of weights $\lambda$ and $\mu$ is a highest weight vector of weight $\lambda + \mu$, and the product is nonzero because $\Omega_n$ is irreducible, so its coordinate ring is an integral domain.
--
--   This semigroup property is the engine that turns a small family of basic shapes into all the shapes needed for the main theorem, and it is reusable for any irreducible orbit closure.
--
--   **Formalization note.** Weights are functions $\mathbb{N}\to\mathbb{N}$ and their sum is pointwise; no partition hypothesis is imposed, so the statement applies to arbitrary weights of the stated degrees.
-- source:
--   P. Bürgisser, C. Ikenmeyer, G. Panova, *No occurrence obstructions in geometric complexity theory*, J. Amer. Math. Soc. 32 (2019), 163–193, https://doi.org/10.1090/jams/908, p. 167, Lemma 2.2.

import Definitions.Def_GCTOcc_occurrence
open MvPolynomial

namespace GCTOcc

theorem occurs_add_of_occurs (n d₁ d₂ : ℕ) (lam mu : ℕ → ℕ)
    (h₁ : Occurs n d₁ lam (orbitClosure n (detPoly n)))
    (h₂ : Occurs n d₂ mu (orbitClosure n (detPoly n))) :
    Occurs n (d₁ + d₂) (fun i => lam i + mu i) (orbitClosure n (detPoly n)) := by sorry

end GCTOcc
