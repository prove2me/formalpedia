-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_split_place_artinValue4_ne
-- name    : LanglandsTunnell.exists_split_place_artinValue4_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/79ae8184-c70a-51a3-9a96-e7977f468271
-- title:
--   Split primes with distinct order-four Artin values
-- statement:
--   Let $L$ be a number field, Galois over $\mathbb{Q}$, and let $e$ be a group isomorphism $\mathrm{Gal}(L/\mathbb{Q}) \simeq \mathrm{GL}_2(\mathbb{Z}/3)$; fix $\zeta \in \mathbb{C}$ with $\zeta^4 = -1$. Two subgroups of $\mathrm{Gal}(L/\mathbb{Q})$ are involved: `quatH e`, the intersection of `sylowH e` — the elements $\gamma$ whose matrix $e(\gamma)$ is the mod-$3$ reduction of a member of the explicit sixteen-element set `P16` — with the kernel of $\det \circ e$; and `c4H e`, the group of integer powers of $(\mathrm{gammaT}\,e)^2$, where $\mathrm{gammaT}\,e = e^{-1}(\mathrm{tbarGL})$. Write $E = L^{\mathrm{quatH}\,e}$ and $K = L^{\mathrm{c4H}\,e}$ for the corresponding fixed fields. For a height-one prime $\mathfrak{P}$ of $\mathcal{O}_K$, $\mathrm{artinValue4}\,e\,h\zeta\,\mathfrak{P} \in \mathbb{C}^\times$ is the value of `chiGal4 e hζ`, the restriction of the character `chiGal e hζ` to `c4H e`, at `seedFrob (c4H e) 𝔓`: the arithmetic Frobenius of $L/\mathbb{Q}$ at a chosen prime of $\mathcal{O}_L$ over $\mathfrak{P}$, raised to the relative degree putting it into `c4H e`. The assertion: for every finite set $S$ of height-one primes of $\mathcal{O}_E$ there exist $v \notin S$ and height-one primes $\mathfrak{P}_1 \neq \mathfrak{P}_2$ of $\mathcal{O}_K$, both lying under $v$, with $\mathrm{artinValue4}\,e\,h\zeta\,\mathfrak{P}_1 \neq \mathrm{artinValue4}\,e\,h\zeta\,\mathfrak{P}_2$.
--
--   This is the non-invariance statement used in Tunnell's octahedral argument: the order-four character of $\mathrm{c4H}\,e$ is not fixed by the nontrivial automorphism of the quadratic extension $K/E$, and this is witnessed at primes of $E$ outside any prescribed finite set which split in $K$ with differing Artin values at the two primes above. It feeds the construction of the quadratic ray class character table for the lift attached to `quatH e`, via [`LanglandsTunnell.exists_quadratic_rayClassChar_table_liftTraceSeed_quatH_of_detDictionaryRow`](thm.html#LanglandsTunnell.exists_quadratic_rayClassChar_table_liftTraceSeed_quatH_of_detDictionaryRow); the proof cites the Frobenius density statement for $L$, the identification of the stabiliser of an unramified prime with the powers of its arithmetic Frobenius, and the existence of a finite set of rational primes outside which all primes of $\mathcal{O}_L$ have trivial inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_split_place_artinValue4_ne.lean

import Definitions.Def_LanglandsTunnell_C4Character

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2

theorem LanglandsTunnell.exists_split_place_artinValue4_ne
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1) :
    ∀ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))), ∃ v ∉ S,
      ∃ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 ↥(fixFld (c4H e))),
      𝔓₁ ≠ 𝔓₂ ∧ 𝔓₁.under (𝓞 ↥(fixFld (quatH e))) = v ∧ 𝔓₂.under (𝓞 ↥(fixFld (quatH e))) = v ∧
      artinValue4 e hζ 𝔓₁ ≠ artinValue4 e hζ 𝔓₂ := by sorry
