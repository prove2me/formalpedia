-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_piFin_range_localizes_of_jqModC_mem
-- name    : ModularCurve.CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/0f240db7-0ed4-522b-afbf-8b0efea4f79a
-- title:
--   Finite chart ring localises to 𝒪ᵥ where jmath̃ is regular
-- statement:
--   Fix $N\ge 1$, a valuation subring $A$ of $\overline{\mathbb Q}$, a prime $\ell$ not dividing $N$, a field $k$ of characteristic $\ell$, a ring homomorphism $\mathrm{red}\colon A\to k$, and a fibre model $fm$ for these data: a pair of subrings $B_{\mathrm{fin}},B_{\infty}$ of the $\overline{\mathbb Q}$-base change `laurentBaseChange` of `modularFunctionFieldFull N`, each containing the constants $\mathrm{image}(A)$ and integral over the corresponding affine base ring, with $\bar\jmath,\bar\jmath_N\in B_{\mathrm{fin}}$ and $\bar\jmath^{-1}\in B_{\infty}$, together with ring homomorphisms $\pi_{\mathrm{fin}},\pi_{\infty}$ into the field `modularFunctionFieldC k N` $=k(\,\mathrm{jqModC}\,k,\ \mathrm{jqNModC}\,k\,N)\subseteq k((q))$ carrying constants to their $\mathrm{red}$-images and $\bar\jmath,\bar\jmath_N,\bar\jmath^{-1}$ to the corresponding reduced $q$-expansions. Let $v$ be a place of `modularFunctionFieldC k N` over $k$, i.e. a proper valuation subring $\mathcal O_v$ containing $k$ which is a principal ideal ring, and assume $\mathrm{jqModC}\,k\in\mathcal O_v$. Then: every $\pi_{\mathrm{fin}}(b)$, $b\in B_{\mathrm{fin}}$, lies in $\mathcal O_v$; and for every $g\in\mathcal O_v$ there are $b,b'\in B_{\mathrm{fin}}$ with $g\cdot\pi_{\mathrm{fin}}(b')=\pi_{\mathrm{fin}}(b)$ and such that $\pi_{\mathrm{fin}}(b')$ does not take the value $0$ at $v$ (its residue in the residue field of $\mathcal O_v$ is not the image of $0$, so by the first assertion it is a unit of $\mathcal O_v$).
--
--   This is the statement that the image under $\pi_{\mathrm{fin}}$ of the $j$-finite chart ring of a fibre model of $X_0(N)$ in characteristic $\ell\nmid N$ consists of functions regular at $v$ and localises, at the centre of $v$, to the full valuation ring $\mathcal O_v$, for every place $v$ at which the reduced $j$-function is regular. It is used by the place-specialisation machinery, in particular by the prolongation-tuple lemmas comparing values and residues of functions at a place of the fibre with those of the $j$-integral closure and with the behaviour at the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_piFin_range_localizes_of_jqModC_mem.lean

import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve ModularCurve.CharPModel

theorem ModularCurve.CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k) (fm : FibreModel N A ℓ k red)
    (v : Place k (modularFunctionFieldC k N))
    (hv : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring) :
    (∀ b : fm.BFin, fm.piFin b ∈ v.toValuationSubring) ∧
      ∀ g : modularFunctionFieldC k N, g ∈ v.toValuationSubring →
        ∃ b b' : fm.BFin, ¬ v.HasValue (fm.piFin b') (0 : k) ∧ g * fm.piFin b' = fm.piFin b := by sorry
