-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_adicCompletionSemialgHom_comp_of_tower
-- name    : IsDedekindDomain.HeightOneSpectrum.adicCompletionSemialgHom_comp_of_tower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/a84e08b7-6402-5996-a5b4-38a7471bea84
-- title:
--   Completion maps compose in a tower of number fields
-- statement:
--   Let $K$, $K'$, $K''$ be number fields with algebra structures $K \to K'$, $K' \to K''$, $K \to K''$ forming a scalar tower, and let $w''$ be a height-one prime of $\mathcal O_{K''}$. Write $w' =$ `HeightOneSpectrum.under (𝓞 K') w''` for the prime of $\mathcal O_{K'}$ lying under $w''$ and $w =$ `HeightOneSpectrum.under (𝓞 K) w'`. Assume $h$: the prime of $\mathcal O_K$ under $w''$ equals $w$. For an element $x$ of the $w$-adic completion of $K$, the assertion is the pointwise equality of two maps into the $w''$-adic completion of $K''$: first, the composite of `HeightOneSpectrum.Extension.adicCompletionSemialgHom K K'` indexed by the element $\langle w', \mathrm{rfl}\rangle$ of `Extension (𝓞 K')` over $w$ (the subtype of primes of $\mathcal O_{K'}$ whose prime under $\mathcal O_K$ is $w$) with `adicCompletionSemialgHom K' K''` indexed by $\langle w'', \mathrm{rfl}\rangle$; second, `adicCompletionSemialgHom K K''` indexed by $\langle w'', h\rangle$, where $h$ witnesses that $w''$ lies in the extension subtype over $w$. These two ring maps $K_w \to K''_{w''}$, each obtained by completing the continuous inclusion of valued fields, take the same value at $x$.
--
--   This is the functoriality in towers of the canonical embeddings of adic completions, $K_w \hookrightarrow K'_{w'} \hookrightarrow K''_{w''}$, with the hypothesis $h$ used to index the long map by $w''$ viewed as a prime above $w$, so that no transport along an equality of places is required. It is used in the local analysis of places in extensions of number fields and in the comparison of local levels, for instance by [`NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion_tower`](thm.html#NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion_tower) and [`M4aHerbrand.Bridge.genuineBeta_comp_of_tower`](thm.html#M4aHerbrand.Bridge.genuineBeta_comp_of_tower).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_adicCompletionSemialgHom_comp_of_tower.lean

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField

theorem IsDedekindDomain.HeightOneSpectrum.adicCompletionSemialgHom_comp_of_tower
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
    (w'' : HeightOneSpectrum (𝓞 K''))
    (h : HeightOneSpectrum.under (𝓞 K) w'' = HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w''))
    (x : (HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'')).adicCompletion K) :
    HeightOneSpectrum.Extension.adicCompletionSemialgHom K' K''
        (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K') w'').Extension (𝓞 K''))
      (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K'
        (⟨HeightOneSpectrum.under (𝓞 K') w'', rfl⟩ :
          (HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'')).Extension (𝓞 K')) x) =
    HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
        (⟨w'', h⟩ : (HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'')).Extension (𝓞 K'')) x := by sorry
