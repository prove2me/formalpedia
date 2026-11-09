-- Prove2me | Theorems.Thm_ModLatSVP_eq_11
-- name    : ModLatSVP.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:24.277669+00:00
-- url     : https://prove2.me/theorems/f4d05a7d-5a15-4676-8a0d-c7180706b19f
-- title:
--   (11) — $|\Delta_F|=|\Delta_E|^{[F:E]}\,\mathrm{Nm}_{E/\mathbb Q}(\mathfrak d_{F/E})$; the root discriminant does not increase in subfields
-- statement:
--   Let $E\subseteq F$ be number fields, and let $\mathfrak d_{F/E}$ be the relative discriminant ideal of $F/E$. Then
--
--   $$|\Delta_F|=|\Delta_E|^{[F:E]}\,\mathrm{Nm}_{E/\mathbb Q}(\mathfrak d_{F/E}),$$
--
--   the norm $\mathrm{Nm}_{E/\mathbb Q}(\mathfrak d_{F/E})$ is a positive integer, and consequently $\mathrm{rd}(E)\le\mathrm{rd}(F)$.
--
--   The paper uses it to see that every field of a subfield chain has root discriminant at most $\mathrm{rd}(K)\le C_0$, so the bound of Lemma 2.3 holds uniformly at every level of the subfield descent.
--
--   Differences from the source:
--   - reading: d_{F/E}, the relative discriminant ideal (not defined in the paper) → Ideal.relNorm (𝓞 E) (differentIdeal (𝓞 E) (𝓞 F)), the relative norm of the different; Nm_{E/ℚ} is Ideal.absNorm; reason: the relative discriminant ideal equals N_{F/E}(𝔇_{F/E}), the standard identity
--   - encoding: E ⊆ F → number fields E, F with an algebra map E → F; reason: a field homomorphism is injective; this is the general form of a subfield
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §3.1, (11), p.17 (PDF p.17); used in the proof of Lemma 3.6, p.22

import Mathlib
import Definitions.Def_ModLatSVP_IsStar

open NumberField

namespace ModLatSVP

/-- **(11), §3.1, p.17: the discriminant in a tower.** Kim, Lee, Son, *Exact SVP and CVP in Structured
Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256
e7151fad…): "The root discriminant does not increase when passing to a subfield. Indeed, for E ⊆ F,
|∆_F| = |∆_E|^{[F:E]} Nm_{E/ℚ}(d_{F/E}), where d_{F/E} is the relative discriminant ideal, whose norm is
a positive integer."

For number fields `E ⊆ F`: `|∆_F| = |∆_E|^{[F:E]} · Nm_{E/ℚ}(d_{F/E})`, the norm `Nm_{E/ℚ}(d_{F/E})` is a
positive integer, and `rd(E) ≤ rd(F)`.

**Formalization Note.** The paper does not define `d_{F/E}`; it is read as the relative norm
`N_{F/E}(𝔇_{F/E})` of the different ideal of `𝒪_F/𝒪_E` (the standard identity for the relative
discriminant), and `Nm_{E/ℚ}` is the absolute ideal norm. `E ⊆ F` is an algebra `E → F`. -/
theorem eq_11 (E F : Type*) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F] :
    (discr F).natAbs = (discr E).natAbs ^ Module.finrank E F *
        Ideal.absNorm (Ideal.relNorm (𝓞 E) (differentIdeal (𝓞 E) (𝓞 F))) ∧
      0 < Ideal.absNorm (Ideal.relNorm (𝓞 E) (differentIdeal (𝓞 E) (𝓞 F))) ∧
      rd E ≤ rd F := by sorry

end ModLatSVP
