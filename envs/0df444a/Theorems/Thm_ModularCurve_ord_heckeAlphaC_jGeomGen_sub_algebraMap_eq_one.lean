-- Prove2me | Theorems.Thm_ModularCurve_ord_heckeAlphaC_jGeomGen_sub_algebraMap_eq_one
-- name    : ModularCurve.ord_heckeAlphaC_jGeomGen_sub_algebraMap_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/38a506a6-2818-51a7-9782-9cecc044507a
-- title:
--   j(mathsf q)-a is a uniformiser on the ℓ-degeneracy roof
-- statement:
--   Let $q'$ be a prime, $k$ an algebraically closed field of characteristic $q'$, and $N,\ell$ nonzero naturals with $\ell$ prime, subject to $\ell\nmid N$, $q'\nmid N$ and $\ell\neq q'$. Write $R=$ `charLDegeneracyRoof k N ℓ` for the intermediate field of $k(\!(\mathsf q)\!)/k$ generated over $k$ by the four Laurent series $j(\mathsf q)$, $j(\mathsf q^{N})$, $j(\mathsf q^{\ell})$, $j(\mathsf q^{N\ell})$ (`jqModC` and its substitutions `jqNModC`), and let $j(\mathsf q)$ denote the element `jGeomGen k N` of $k(j(\mathsf q),j(\mathsf q^{N}))=$ `modularFunctionFieldC k N`, transported into $R$ by the inclusion `heckeAlphaC`. Let $y$ be a place of $R$ over $k$, i.e. a valuation subring of $R$ containing $k$, not all of $R$, and a principal ideal ring. Assume $j(\mathsf q)$ lies in that valuation subring, that its value `y.evalAt` (the residue class of $j(\mathsf q)$, pulled back to $k$) equals $a\in k$, and that $a\neq 0$ and $a\neq 1728$. Then the normalised order $\operatorname{ord}_y\bigl(j(\mathsf q)-a\bigr)$, i.e. $-\log$ of the adic valuation attached to $y$, equals $1$. The proof uses neither the hypothesis $\ell\nmid N$ nor the integrality hypothesis on $j(\mathsf q)$.
--
--   This records, in the vocabulary of the $\ell$-degeneracy roof, that the geometric $j$-function minus a value avoiding $0$ and $1728$ is a uniformiser at a place of the roof: the $j$-line cover is unramified away from the elliptic points. It is used in the order computations on the roof, in particular in [`ModularCurve.ord_heckeMultiplier_eq_zero_of_evalAt_ne`](thm.html#ModularCurve.ord_heckeMultiplier_eq_zero_of_evalAt_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_heckeAlphaC_jGeomGen_sub_algebraMap_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.ord_heckeAlphaC_jGeomGen_sub_algebraMap_eq_one
    (q' : ℕ) [Fact q'.Prime] (k : Type*) [Field k] [CharP k q'] [IsAlgClosed k]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hq'N : ¬ q' ∣ N) (hq'ℓ : ℓ ≠ q')
    (y : Place k ↥(charLDegeneracyRoof k N ℓ))
    (hy : heckeAlphaC k N ℓ (jGeomGen k N) ∈ y.toValuationSubring)
    (a : k) (ha : y.evalAt (heckeAlphaC k N ℓ (jGeomGen k N)) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    y.ord (heckeAlphaC k N ℓ (jGeomGen k N) - algebraMap k ↥(charLDegeneracyRoof k N ℓ) a) = 1 := by sorry
