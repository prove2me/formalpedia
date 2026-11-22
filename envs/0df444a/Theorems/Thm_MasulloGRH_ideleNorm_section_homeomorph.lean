-- Prove2me | Theorems.Thm_MasulloGRH_ideleNorm_section_homeomorph
-- name    : MasulloGRH.ideleNorm_section_homeomorph
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:42.852351+00:00
-- url     : https://prove2.me/theorems/45eb6bd6-c5fa-4ebb-bd52-21e413dfafab
-- title:
--   Lemma A.2.2.9 — a continuous homomorphic section $s$ of the idelic norm splits $\mathrm{GL}_1(\mathbb A_F)\cong\mathbb R_{>0}\times\mathrm{GL}_1(\mathbb A_F)^1$ via $(t,g_0)\mapsto s(t)g_0$
-- statement:
--   **Splitting of the idele group by a continuous homomorphic section of the idelic norm** (Lemma A.2.2.9, eq. (A.2.2.12) of the source).
--
--   Let $F$ be a number field, $\mathbb I_F=\mathrm{GL}_1(\mathbb A_F)$ its idele group with the idele topology, $|\cdot|_F\colon\mathbb I_F\to\mathbb R_{>0}$, $|g|_F=\prod_v|g_v|_v$, the idelic norm, and $\mathbb I_F^1=\ker|\cdot|_F$ the closed subgroup of norm-one ideles with the induced topology. Let
--   $$s\colon\mathbb R_{>0}\to\mathbb I_F$$
--   be a continuous group homomorphism which is a section of the idelic norm: $|s(t)|_F=t$ for all $t>0$. Then the map
--   $$\theta_{F,s}\colon\mathbb R_{>0}\times\mathbb I_F^1\longrightarrow\mathbb I_F,\qquad\theta_{F,s}(t,g_0)=s(t)\,g_0,$$
--   is a homeomorphism. Since $\theta_{F,s}$ is visibly a group homomorphism ($s$ is one and $\mathbb I_F$ is commutative), it is an isomorphism of Hausdorff locally compact abelian groups, with inverse $g\mapsto\big(|g|_F,\ s(|g|_F)^{-1}g\big)$.
--
--   Examples of such sections are the canonical section $s_F$ (all archimedean components equal to $t^{1/[F:\mathbb Q]}$, finite components $1$), the section $s_{F,v_0}$ along one archimedean place and the diagonal section $s_{F,\delta}$ (Lemmas A.2.2.4, A.2.2.6, A.2.2.8 of the source). The decomposition is used constantly: it descends to $C_F\cong\mathbb R_{>0}\times C_F^1$ for the idele class group, shows that every quasi-character of $C_F$ is a character of the compact group $C_F^1$ times a power $|\cdot|_F^s$, and lets Haar integrals over $\mathbb I_F$ be written as iterated integrals over $\mathbb R_{>0}$ and $\mathbb I_F^1$.
--
--   **Deviation from the source.** The lemma is printed for "any continuous section $s$ to the idelic norm", but the map $\theta_{F,s}$ is a homomorphism only if $s$ is one; the hypothesis that $s$ is a continuous *homomorphic* section, which is the standing convention announced at the beginning of §A.2.2 of the source, is stated explicitly.
--
--   **Formalization Note.** $\mathbb I_F$ is `MasulloGRH.IdeleGroup F = (AdeleRing (𝓞 F) F)ˣ` with the units topology and $|\cdot|_F$ is the platform's real-valued function `MasulloGRH.ideleNorm`. The topological group $\mathbb R_{>0}$ is modelled by `ℝ≥0ˣ` (the units of the non-negative reals), so $s$ is a monoid homomorphism `ℝ≥0ˣ →* IdeleGroup F` and the section property reads `ideleNorm (s t) = t`. Because `ideleNorm` is a plain function, $\mathbb I_F^1$ is the subtype `{g // ideleNorm g = 1}` with the subspace topology rather than a bundled subgroup; the conclusion is therefore stated as the existence of a homeomorphism `θ` with the prescribed formula `θ (t, g) = s t * g`, which carries the whole content (multiplicativity of this formula is immediate).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 547, Lemma A.2.2.9, eq. (A.2.2.12) (continuous homomorphic sections are defined at the head of §A.2.2, p. 546)

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm

open NumberField IsDedekindDomain
open scoped NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem ideleNorm_section_homeomorph (F : Type*) [Field F] [NumberField F]
    (s : ℝ≥0ˣ →* IdeleGroup F) (hs : Continuous s)
    (hsec : ∀ t : ℝ≥0ˣ, ideleNorm (s t) = ((t : ℝ≥0) : ℝ)) :
    ∃ θ : (ℝ≥0ˣ × {g : IdeleGroup F // ideleNorm g = 1}) ≃ₜ IdeleGroup F,
      ∀ (t : ℝ≥0ˣ) (g : {g : IdeleGroup F // ideleNorm g = 1}),
        θ (t, g) = s t * (g : IdeleGroup F) := by sorry

end MasulloGRH
