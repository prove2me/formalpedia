-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_resolventSignChar_sylowH
-- name    : LanglandsTunnell.exists_resolventSignChar_sylowH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/4c33e9c5-7d4d-509c-8687-c4baa2a2b750
-- title:
--   Sign character of a GL₂(𝔽₃)-tower over ℚ
-- statement:
--   Let $L$ be a number field that is Galois over $\mathbb{Q}$ and let $e$ be an isomorphism of groups from $\mathrm{Gal}(L/\mathbb{Q})$ onto $GL_2(\mathbb{Z}/3)$. The assertion is that there exist a finite set $S_0$ of height-one primes of the ring of integers of $\mathbb{Q}$ and a function $\chi$ from the height-one spectrum of that ring to $\mathbb{C}$ with the following five properties, each for every height-one prime $v \notin S_0$. First, for every maximal ideal $Q$ of $\mathcal{O}_L$ whose contraction to the integers of $\mathbb{Q}$ is $v$ and every $\sigma \in \mathrm{Gal}(L/\mathbb{Q})$ that is an arithmetic Frobenius at $Q$ (in the sense of `IsArithFrobAt`), one has $\chi(v) = 1$ if and only if $\sigma$ lies in `detKer e`, the kernel of the composite of $e$ with the determinant $GL_2(\mathbb{Z}/3) \to (\mathbb{Z}/3)^\times$, and $\chi(v) = -1$ if and only if $\sigma$ does not lie in that kernel. Second, $\chi(v)^2 = 1$. Third, $\chi(v) = 1$ if and only if some height-one prime $\mathfrak{P}$ of the ring of integers of the fixed field of `detKer e` contracts to $v$ and has `inertiaDeg'` equal to $1$ over it. Fourth, $\chi(v) = 1$ if and only if every height-one prime $\mathfrak{P}$ of the ring of integers of the fixed field of the subgroup `sylowH e` — the elements $\gamma$ for which the matrix of $e\gamma$ is the entrywise image under `red` of some matrix belonging to the explicit set `P16` — contracting to $v$ has `inertiaDeg'` different from $2$. Fifth, every maximal ideal of $\mathcal{O}_L$ contracting to $v$ has trivial inertia subgroup in $\mathrm{Gal}(L/\mathbb{Q})$.
--
--   This packages the quadratic resolvent character of a $GL_2(\mathbb{F}_3)$-extension of $\mathbb{Q}$: away from a finite set of primes, the sign $\det e(\mathrm{Frob}_v)$ is recorded by a $\pm 1$-valued function $\chi$, and the Dedekind–Frobenius description of residue degrees identifies $\chi(v)=1$ both with the existence of a degree-one prime in the fixed field of the determinant kernel and with the absence of a residue degree $2$ prime in the fixed field of `sylowH e`. It is used in the Langlands–Tunnell portion of the argument, by [`LanglandsTunnell.exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH`](thm.html#LanglandsTunnell.exists_resolventSign_not_agreesAwayFromFinite_twist_sylowH_of_liftTraceSeed_quatH); the finiteness of the ramified set comes from [`LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_ne_bot_dvd`](thm.html#LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_ne_bot_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_resolventSignChar_sylowH.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain LanglandsTunnell

theorem LanglandsTunnell.exists_resolventSignChar_sylowH
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (χ : HeightOneSpectrum (𝓞 ℚ) → ℂ),
      (∀ v ∉ S₀, ∀ (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal →
          IsArithFrobAt (𝓞 ℚ) σ Q → (χ v = 1 ↔ σ ∈ detKer e) ∧ (χ v = -1 ↔ σ ∉ detKer e)) ∧
      (∀ v ∉ S₀, χ v * χ v = 1) ∧
      (∀ v ∉ S₀, (χ v = 1 ↔ ∃ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (detKer e))),
          𝔓.under (𝓞 ℚ) = v ∧ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal = 1)) ∧
      (∀ v ∉ S₀, (χ v = 1 ↔ ∀ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e))), 𝔓.under (𝓞 ℚ) = v →
          (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 2)) ∧
      (∀ v ∉ S₀, ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal → Q.inertia (L ≃ₐ[ℚ] L) = ⊥) := by sorry
