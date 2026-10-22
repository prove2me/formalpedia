-- Prove2me | Theorems.Thm_Hatcher_Singular_excision
-- name    : Hatcher.Singular.excision
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-21T08:26:25.740299+00:00
-- url     : https://prove2.me/theorems/5a98dacc-d129-420a-a544-b256ce5a8972
-- title:
--   Excision for singular homology with coefficients in a ring
-- statement:
--   Let $R$ be a ring and $X$ a topological space. Let $Z\subseteq A\subseteq X$ be subsets such that the closure of $Z$ is contained in the interior of $A$. Then the inclusion of pairs $(X\setminus Z,\,A\setminus Z)\hookrightarrow(X,A)$ induces isomorphisms
--   $$H_n(X\setminus Z,\,A\setminus Z;R)\ \xrightarrow{\ \cong\ }\ H_n(X,A;R)\qquad\text{for all } n\ge 0.$$
--
--   Here $H_n(\cdot,\cdot;R)$ is relative singular homology with coefficients in $R$, and $X\setminus Z$, $A\setminus Z$ carry the subspace topologies.
--
--   Excision is one of the basic axioms of homology: it allows one to cut out a well-behaved subset without changing relative homology, and it is the main input of the Mayer–Vietoris sequence and of the computation of the homology of spheres.
--
--   **Formalization Note** The statement only assumes $\overline Z\subseteq\operatorname{int}A$; the inclusion $Z\subseteq A$ follows. $X\setminus Z$ is the subtype of the complement of $Z$, and $A\setminus Z$ is the preimage of $A$ in it; the conclusion is that the induced map of relative homology groups is an isomorphism in the category of $R$-modules.
-- source:
--   A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002 (online edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1, Theorem 2.20 (p. 119), stated there for integer coefficients; arbitrary coefficients as in §2.2, “Homology with Coefficients” (p. 153). Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Bridge/Singular/Excision.lean`.

import Mathlib
import Definitions.Def_Hatcher_SingularHomology

open CategoryTheory

theorem Hatcher.Singular.excision (R : Type) [Ring R] (X : Type) [TopologicalSpace X] (A Z : Set X)
    (hZA : closure Z ⊆ interior A) (n : ℕ) :
    IsIso (relMap R n (incl Zᶜ) (Subtype.val ⁻¹' A : Set (Zᶜ : Set X)) A
      (fun _ hx ↦ hx)) := by sorry
