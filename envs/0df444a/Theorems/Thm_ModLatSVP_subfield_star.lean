-- Prove2me | Theorems.Thm_ModLatSVP_subfield_star
-- name    : ModLatSVP.subfield_star
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:11.73532+00:00
-- url     : https://prove2.me/theorems/e8fb6374-5edd-4759-b87a-b58bbf18fbda
-- title:
--   Subfields of a totally real or CM field — $\star$ restricts, and every subfield is totally real or CM
-- statement:
--   Let $K$ be a totally real or CM field with involution $\star$, and let $E$ be a subfield of $K$. Then
--
--   1. $x^\star\in E$ for every $x\in E$;
--   2. the restriction of $\star$ to $E$ acts as complex conjugation under every embedding of $E$: $\sigma(x^\star)=\overline{\sigma(x)}$ for every $\sigma:E\to\mathbb C$;
--   3. $E$ is totally real or CM.
--
--   This is why the subfields found or supplied in a chain carry an involution and satisfy the hypotheses of the paper's algorithms; it is used in the proof of Lemma 3.6.
--
--   Differences from the source:
--   - encoding: a subfield E of K; the restricted involution → an intermediate field E of K/ℚ; an automorphism τ_E of E agreeing with τ on E and satisfying IsStar; reason: Mathlib's representation of subfields
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), proof of Lemma 3.6, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_ModLatSVP_IsStar

open NumberField

namespace ModLatSVP

/-- **Subfields of a totally real or CM field, proof of Lemma 3.6, p.22.** Kim, Lee, Son, *Exact SVP and
CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript
sha256 e7151fad…): "The involution ⋆ restricts to every subfield E. Indeed, for x ∈ E and every
embedding σ of K, σ(x⋆) = conj(σ(x)) depends only on σ|_E. Thus every automorphism of a normal closure
fixing E also fixes x⋆, proving x⋆ ∈ E. The restricted involution acts as complex conjugation under every
embedding of E, so E is totally real or CM."

For `K` totally real or CM with involution `τ` and every subfield `E` of `K`:
1. `τ` maps `E` into `E`;
2. the restriction `τ_E` of `τ` to `E` is an involution of `E` in the sense of `IsStar`;
3. `E` is totally real or CM. -/
theorem subfield_star (K : Type*) [Field K] [NumberField K] (hK : IsTotallyReal K ∨ IsCMField K)
    (τ : K ≃ₐ[ℚ] K) (hτ : IsStar K τ) (E : IntermediateField ℚ K) :
    (∀ x ∈ E, τ x ∈ E) ∧
      ∃ τE : E ≃ₐ[ℚ] E, (∀ x : E, ((τE x : E) : K) = τ x) ∧ IsStar E τE ∧
        (IsTotallyReal E ∨ IsCMField E) := by sorry

end ModLatSVP
