-- Prove2me | Theorems.Thm_M4aLocalCFT_fieldUnitsDecomp_norm_ker_le_derive_range
-- name    : M4aLocalCFT.fieldUnitsDecomp_norm_ker_le_derive_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/2469daf1-180c-568a-8f2f-8f6d0777a256
-- title:
--   Cyclic Hilbert 90 for a decomposition group on L^×
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $A$ be a valuation subring of $L$ whose decomposition subgroup $D = A.\mathrm{decompositionSubgroup}\ K \le L \simeq_{\mathrm{alg}[K]} L$ is finite. Let $g \in D$ be such that every element of $D$ lies in the subgroup of integer powers of $g$, i.e. $g$ generates $D$ (so $D$ is cyclic). Two group homomorphisms $L^\times \to L^\times$ are in play: `fieldUnitsNorm` $A$, the pointwise product over $s \in D$ of the maps $x \mapsto s(x)$ induced on units by the $K$-algebra automorphisms $s$, that is $x \mapsto \prod_{s \in D} s(x)$; and `fieldUnitsDerive` $A$ $g$, the quotient of $x \mapsto g(x)$ by the identity, that is $x \mapsto g(x)\,x^{-1}$. The assertion is an inclusion of subgroups of $L^\times$: the kernel of `fieldUnitsNorm` $A$ is contained in the range of `fieldUnitsDerive` $A$ $g$; equivalently, every $x \in L^\times$ with $\prod_{s \in D} s(x) = 1$ can be written as $g(y)\,y^{-1}$ for some $y \in L^\times$. No discreteness or completeness hypothesis on $A$ is imposed; $A$ enters only through the group $D$.
--
--   This is Hilbert's Theorem 90 in its cyclic form, transported to the action of a finite cyclic decomposition group $D$ on $L^\times$, with the product over $D$ playing the role of the norm and $x \mapsto g(x)x^{-1}$ the role of the coboundary map. It is used in the computation of the zeroth Tate cohomology group of $L^\times$ for the decomposition group, and thence in the local analysis at a place of a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aLocalCFT_fieldUnitsDecomp_norm_ker_le_derive_range.lean

import Definitions.Def_M4aLocalCFT_VocabDefs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem M4aLocalCFT.fieldUnitsDecomp_norm_ker_le_derive_range
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Finite (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (M4aLocalCFT.fieldUnitsNorm (K := K) A).ker ≤
      (M4aLocalCFT.fieldUnitsDerive A g).range := by sorry
