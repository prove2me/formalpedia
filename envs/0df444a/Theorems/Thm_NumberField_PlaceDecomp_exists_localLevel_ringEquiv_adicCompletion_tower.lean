-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion_tower
-- name    : NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion_tower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/612f15e4-60ca-5b84-95c7-89a89c000d8c
-- title:
--   Compatible q-adic models of completions in a tower of places
-- statement:
--   Let $E$, $K$, $K''$ be number fields with $K$ an $E$-algebra, $K''$ a $K$-algebra and an $E$-algebra forming a scalar tower over $E$ and $K$, with both $K''/E$ and $K/E$ Galois, and let $w''$ be a height one prime of $\mathcal{O}_{K''}$; write $w$ for $w''$ contracted to $\mathcal{O}_K$, i.e. `HeightOneSpectrum.under (𝓞 K) w''`. The assertion is the existence of a prime $q$, of two intermediate fields $L \le L''$ of the algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, both finite-dimensional over $\mathbb{Q}_q$, together with: a faithful multiplicative semiring action of the decomposition group `decomp E K w`, that is the stabiliser in $K \simeq_{\mathrm{alg}[E]} K$ of the valuation subring of the $w$-adic valuation on $K$, on $L$, and a compatible multiplicative, distributive action of that group on $L^\times$; likewise a faithful multiplicative semiring action of `decomp E K'' w''`, the corresponding stabiliser in $K'' \simeq_{\mathrm{alg}[E]} K''$, on $L''$ and on $(L'')^\times$; and ring isomorphisms $\Phi \colon K_w \xrightarrow{\sim} L$ and $\Phi'' \colon K''_{w''} \xrightarrow{\sim} L''$ of the respective adic completions. These data satisfy: $\Phi$ and $\Phi''$ are equivariant for the two decomposition-group actions; both actions fix the image of $\mathbb{Q}_q$ pointwise; the actions on units are compatible with the inclusions of $L^\times$ into $L$ and of $(L'')^\times$ into $L''$; the square commutes, in the sense that for every $x \in K_w$ the image in `PadicAlgCl q` of $\Phi''$ applied to the canonical semialgebra map $K_w \to K''_{w''}$ attached to the extension $\langle w'', \mathrm{rfl}\rangle$ of $w$ equals the image of $\Phi x$; and finally $q$, viewed in $\mathcal{O}_{K''}$, lies in the ideal of $w''$, so that $q$ is the residue characteristic.
--
--   This packages the local fields $K_w$ and $K''_{w''}$ as nested finite extensions of $\mathbb{Q}_q$ inside one fixed algebraic closure, with the decomposition groups acting through $\mathbb{Q}_q$-automorphisms and the canonical map of completions realised as the inclusion $L \subseteq L''$; it is the two-layer version of the single-place bridge. It is used in the Herbrand-quotient and local-fundamental-class computations, where statements about Galois cohomology of the units of a local field must be transported simultaneously to both completions and along the map between them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion_tower.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion_tower
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K''] [IsGalois E K]
    (w'' : HeightOneSpectrum (𝓞 K'')) :
    ∃ (q : ℕ) (_ : Fact q.Prime) (L L'' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : L ≤ L'')
      (_ : FiniteDimensional ℚ_[q] L) (_ : FiniteDimensional ℚ_[q] L'')
      (_ : MulSemiringAction (decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) L)
      (_ : FaithfulSMul (decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) L)
      (_ : MulDistribMulAction (decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) (↥L)ˣ)
      (_ : MulSemiringAction (decomp E K'' w'') L'') (_ : FaithfulSMul (decomp E K'' w'') L'')
      (_ : MulDistribMulAction (decomp E K'' w'') (↥L'')ˣ)
      (Φ : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K ≃+* L) (Φ'' : w''.adicCompletion K'' ≃+* L''),
      (∀ (g : decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) (x : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K),
          Φ (g • x) = g • Φ x) ∧
      (∀ (g : decomp E K'' w'') (x : w''.adicCompletion K''), Φ'' (g • x) = g • Φ'' x) ∧
      (∀ (g : decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) ∧
      (∀ (g : decomp E K'' w'') (x : ℚ_[q]), g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x) ∧
      (∀ (g : decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)) ∧
      (∀ (g : decomp E K'' w'') (u : (↥L'')ˣ), ((g • u : (↥L'')ˣ) : L'') = g • (u : L'')) ∧
      (∀ x : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K,
        ((Φ'' (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
            (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K'')) x) : L'') : PadicAlgCl q) =
          ((Φ x : L) : PadicAlgCl q)) ∧
      ((q : ℕ) : 𝓞 K'') ∈ w''.asIdeal := by sorry
