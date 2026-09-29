-- Prove2me | Theorems.Thm_Matrix_span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul
-- name    : Matrix.span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/b2cd9854-1d08-5e46-aa31-6651baa51325
-- title:
--   Odd irreducible two-dimensional representations span M₂ after base change
-- statement:
--   Let $G$ be a group and $F$ a field in which $2 \neq 0$, and let $\rho \colon G \to M_2(F)$ be a monoid homomorphism into the multiplicative monoid of $2 \times 2$ matrices over $F$. Two hypotheses are imposed. First, an oddness condition: there is $c \in G$ with $\rho(c)\rho(c) = 1$ and $\det \rho(c) = -1$. Second, an irreducibility condition in the form of the absence of a common eigenvector: for every nonzero $v \in F^2$ there is $\sigma \in G$ such that $\rho(\sigma) v \neq c \cdot v$ for all scalars $c \in F$. Let $k$ be a further field and $\iota \colon F \to k$ a ring homomorphism. The conclusion is that the $k$-submodule of $M_2(k)$ spanned by the set of entrywise images $\iota(\rho(g))$, as $g$ ranges over $G$, is all of $M_2(k)$. Taking $\iota$ to be the identity gives that $\rho(G)$ spans $M_2(F)$ over $F$, so that $\rho$ is absolutely irreducible.
--
--   This is Burnside's spanning criterion in the shape used for odd two-dimensional representations in residue characteristic different from $2$, as in the Boston–Lenstra–Ribet analysis of quotients of group rings. It supplies the "image spans the full matrix algebra" hypothesis to the comparison of spans of toric monodromy parts on modular curves, and its proof invokes [`Matrix.span_image_map_eq_top_of_span_eq_top`](thm.html#Matrix.span_image_map_eq_top_of_span_eq_top), which propagates a spanning set of $M_n(k)$ along a homomorphism of fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul
    {G : Type*} [Group G] {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (ρ : G →* Matrix (Fin 2) (Fin 2) F)
    (hodd : ∃ c : G, ρ c * ρ c = 1 ∧ (ρ c).det = -1)
    (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ σ : G, ∀ c : F, (ρ σ).mulVec v ≠ c • v)
    {k : Type*} [Field k] (ι : F →+* k) :
    Submodule.span k (Set.range fun g : G => (ρ g).map ι) = ⊤ := by sorry
