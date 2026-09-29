-- Prove2me | Theorems.Thm_NumberField_AdeleRing_free_of_pi_linearEquiv_pi
-- name    : NumberField.AdeleRing.free_of_pi_linearEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/47c5ba4a-d175-58c3-9b70-9f08456f0c97
-- title:
--   Freeness over the adele ring from a free multiple
-- statement:
--   Let $F$ be a number field, i.e. a field of characteristic zero that is finite-dimensional over $\mathbb{Q}$, and let $\mathbb{A}_F$ denote the adele ring `AdeleRing (𝓞 F) F` attached to $F$ and its ring of integers. Let $m$ and $n$ be natural numbers with $n > 0$, and let $P$ be an additive commutative group equipped with the structure of a module over $\mathbb{A}_F$. Assume that there is an isomorphism of $\mathbb{A}_F$-modules
--   $$f : (\mathrm{Fin}\,n \to P) \;\xrightarrow{\ \sim\ }\; (\mathrm{Fin}\,(m n) \to \mathbb{A}_F),$$
--   that is, the $n$-fold direct sum $P^{n}$ is isomorphic to the free $\mathbb{A}_F$-module of rank $mn$ with its standard basis indexed by $\mathrm{Fin}(mn)$. The conclusion is that $P$ is a free $\mathbb{A}_F$-module, in the sense of `Module.Free`: $P$ admits a basis over $\mathbb{A}_F$. No assertion is made about the index set of such a basis; in particular the rank $m$ predicted by the hypothesis is not part of the statement, nor is any finiteness of the basis claimed explicitly.
--
--   This is the form in which the triviality of finitely generated projective modules of constant rank over the adele ring of a number field ("vector bundles over $\mathbb{A}_F$ are trivial") is used: a module whose $n$-fold sum is free of rank $mn$ is free. It is invoked in the adelic theory of automorphic forms, in the analysis of $\sigma$-conjugacy for adelic actions and in the rank-two case of the corresponding statement about norm strings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_free_of_pi_linearEquiv_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.AdeleRing.free_of_pi_linearEquiv_pi
    (F : Type) [Field F] [NumberField F] (m n : ℕ) (hn : 0 < n)
    (P : Type) [AddCommGroup P] [Module (AdeleRing (𝓞 F) F) P]
    (f : (Fin n → P) ≃ₗ[AdeleRing (𝓞 F) F] (Fin (m * n) → AdeleRing (𝓞 F) F)) :
    Module.Free (AdeleRing (𝓞 F) F) P := by sorry
