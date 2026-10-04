-- Prove2me | Theorems.Thm_MSKleene_free_universal
-- name    : MSKleene.free_universal
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:29:58.621988+00:00
-- url     : https://prove2.me/theorems/d8fccbac-eb3d-4a2b-87b8-67cce1811468
-- title:
--   Proposition 3.5: universal property of the free algebra
-- statement:
--   **Universal property of the free algebra** (Proposition 3.5).
--
--   The pair $(\eta^{X},\mathbf{T}_{\Sigma}(X))$ has the universal property: for every $\Sigma$-algebra $\mathbf{A}$ and every $S$-sorted mapping $f\colon X\to A$ there exists a unique homomorphism $f^{\sharp}\colon\mathbf{T}_{\Sigma}(X)\to\mathbf{A}$ such that $f^{\sharp}\circ\eta^{X}=f$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Term

namespace MSKleene

/-- **Universal property of the free many-sorted algebra** (Proposition 3.5).

For every `Σ`-algebra `A` and every `S`-sorted map `ρ : X → A`, there is a
unique `Σ`-homomorphism `ρ^♯ : T_Σ(X) → A` with `ρ^♯ ∘ η^X = ρ`. -/
theorem free_universal {S : Type} (sig : Signature S) (X : SSet S)
    (A : Algebra sig) (ρ : SMap X A.carrier) :
    ∃! g : Hom (freeAlgebra sig X) A,
      ∀ (s : S) (x : X s), g.toFun s (eta sig X s x) = ρ s x := by
  sorry

end MSKleene
