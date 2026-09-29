-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/346a07d8-def6-581c-922e-e515f9036439
-- title:
--   A field base change M⊗_F Fᵥ forces a unique place above v
-- statement:
--   Let $F$ and $M$ be fields in `Type` that are number fields, with $M$ an $F$-algebra, and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_F$, with $v$-adic completion $F_v =$ `v.adicCompletion F`. Form the tensor product $M \otimes_F F_v$, regarded as an $F_v$-algebra through its right-hand factor, and assume it is a field (the predicate `IsField`). The assertion is that there exist an element $w$ of `v.Extension (𝓞 M)`, i.e. a height-one prime of $\mathcal{O}_M$ whose contraction to $\mathcal{O}_F$ is $v$, and an isomorphism of $F_v$-algebras $e \colon M \otimes_F F_v \xrightarrow{\sim} M_w$ onto the $w$-adic completion `w.1.adicCompletion M`, such that three things hold: every height-one prime $w'$ of $\mathcal{O}_M$ contracting to $v$ equals $w$ (so $w$ is the unique such prime); $e(x \otimes_F 1)$ is the image of $x$ under the structure map $M \to M_w$ for every $x \in M$; and the $F_v$-dimension of $M_w$ equals the $F$-dimension of $M$, both expressed with `Module.finrank`.
--
--   This is the degenerate case of the classical decomposition $M \otimes_F F_v \cong \prod_{w \mid v} M_w$ for a finite extension of number fields: the base change is a field exactly when $v$ has a single extension to $M$, and then it is that single completion, of local degree $[M:F]$. It is used in the project to recognise local fields obtained as quadratic base changes ([`IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare`](thm.html#IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare)) and in a norm-valuation computation over such a base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor.lean

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor
    (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    (v : HeightOneSpectrum (𝓞 F)) (hA : IsField (M ⊗[F] v.adicCompletion F)) :
    ∃ (w : v.Extension (𝓞 M))
      (e : (M ⊗[F] v.adicCompletion F) ≃ₐ[v.adicCompletion F] w.1.adicCompletion M),
      (∀ w' : v.Extension (𝓞 M), w' = w) ∧
      (∀ x : M, e (x ⊗ₜ[F] 1) = algebraMap M (w.1.adicCompletion M) x) ∧
      Module.finrank (v.adicCompletion F) (w.1.adicCompletion M) = Module.finrank F M := by sorry
