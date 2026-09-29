-- Prove2me | Theorems.Thm_ModularCurve_ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq
-- name    : ModularCurve.ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/81dbf62b-7052-583b-bec0-9427240f0d46
-- title:
--   Ring maps out of K(̃ j,̃ j_N) are determined by generators
-- statement:
--   Let $K$ be a field and $N$ a positive natural number, and let $F = \mathtt{modularFunctionFieldC}\,K\,N$ be the intermediate field of the Laurent series field $K((q))$ obtained by adjoining to $K$ the two elements $\tilde j = \mathtt{jqModC}\,K$, namely $q^{-1}$ times the power series with coefficients the images in $K$ of the integer coefficients of $\mathtt{jNum}$, and $\tilde j_N = \mathtt{jqNModC}\,K\,N$, the series obtained from $\tilde j$ by the substitution $q \mapsto q^N$ given by $\mathtt{qExpand}\,K\,N$. Let $S$ be a division ring and let $\varphi, \psi : F \to S$ be ring homomorphisms (not assumed $K$-linear). Assume: (i) $\varphi$ and $\psi$ agree on the constants, i.e. $\varphi(\iota(a)) = \psi(\iota(a))$ for every $a \in K$, where $\iota$ is the structure map $K \to F$; (ii) $\varphi$ and $\psi$ agree on the element `jGeomGen K N` of $F$, which is $\tilde j$ together with the proof that it lies in $F$; (iii) $\varphi$ and $\psi$ agree on `jNGeomGen K N`, which is $\tilde j_N$ similarly viewed in $F$. The conclusion is $\varphi = \psi$.
--
--   A generation statement for the level-$N$ modular function field: since $F$ is by definition generated over $K$ by the two $q$-expansions, any two ring homomorphisms out of $F$ into a division ring that agree on $K$ and on the two generators coincide. It is used in the comparison of identifications of the function field of the level-$N$ modular curve, in particular in the construction of an algebra equivalence matching prescribed values on `jGeomGen` and in the permutation statement comparing the Hecke correspondences $\alpha$ and $\beta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq
    (K : Type*) [Field K] (N : ℕ) [NeZero N] {S : Type*} [DivisionRing S]
    (φ ψ : ↥(modularFunctionFieldC K N) →+* S)
    (hK : ∀ a : K, φ (algebraMap K ↥(modularFunctionFieldC K N) a) = ψ (algebraMap K ↥(modularFunctionFieldC K N) a))
    (hj : φ (jGeomGen K N) = ψ (jGeomGen K N)) (hjN : φ (jNGeomGen K N) = ψ (jNGeomGen K N)) :
    φ = ψ := by sorry
