-- Prove2me | Theorems.Thm_MasulloGRH_schwartz_S_adeles_structure
-- name    : MasulloGRH.schwartz_S_adeles_structure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:48:24.586944+00:00
-- url     : https://prove2.me/theorems/f109f86e-22f1-4a0c-85a0-010f50af871d
-- title:
--   Proposition 2.1.4.1 (2), (4), (5) — structure of $\mathcal S(\mathbb A_{F,S})$ and the embeddings $\pi_S\colon\mathcal S(\mathbb A_{F,S})\to\mathcal S(\mathbb A_F)$
-- statement:
--   Let $F$ be a number field and $S$ a finite set of places containing the Archimedean places. Let $\mathcal S(\mathbb A_{F,S})$ and $\mathcal S(\mathbb A_F)$ be the Schwartz–Bruhat spaces of the $S$-adeles and of the adeles.
--
--   1. $\mathcal S(\mathbb A_{F,S})$ is a strict locally convex inductive limit of a sequence of nuclear Fréchet spaces. It is Hausdorff, complete, nuclear and Montel, and its strong dual is complete, nuclear and Montel.
--   2. The map
--   $$\pi_S\colon\mathcal S(\mathbb A_{F,S})\to\mathcal S(\mathbb A_F),\qquad\pi_S(f)=f\otimes\mathbf 1_{\prod_{v\notin S}\mathcal O_{F_v}},$$
--   i.e. $\pi_S(f)(x)=f(x_S)$ if $x_v\in\mathcal O_{F_v}$ for all $v\notin S$ and $\pi_S(f)(x)=0$ otherwise, is well defined, linear, and a topological embedding.
--   3. Every $f\in\mathcal S(\mathbb A_F)$ is of the form $\pi_T(f_0)$ for some finite set of places $T$ containing the Archimedean places and some $f_0\in\mathcal S(\mathbb A_{F,T})$.
--
--   These statements express $\mathcal S(\mathbb A_F)$ as the union of the spaces $\mathcal S(\mathbb A_{F,S})$, which is how global statements are reduced to $S$-local ones in the draft.
--
--   **Formalization Note** $x_S$ is the projection of the adele $x$ to its coordinates at the places of $S$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.1.4, Proposition 2.1.4.1, parts (2), (4) for S' the set of all places, and the surjectivity statement of (5), eqs. (2.1.4.4)–(2.1.4.5), p. 71

import Definitions.Def_MasulloGRH_ThetaSpaces

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain
open Classical

theorem schwartz_S_adeles_structure (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (IsStrictLFOfNuclearFrechet (SAdelicSchwartz F Sf) ∧ IsHLCS (SAdelicSchwartz F Sf) ∧
      IsCompleteTVS (SAdelicSchwartz F Sf) ∧ IsNuclear (SAdelicSchwartz F Sf) ∧
      IsMontel (SAdelicSchwartz F Sf) ∧
      IsCompleteTVS (StrongDual ℂ (SAdelicSchwartz F Sf)) ∧
      IsNuclear (StrongDual ℂ (SAdelicSchwartz F Sf)) ∧
      IsMontel (StrongDual ℂ (SAdelicSchwartz F Sf))) ∧
    (∃ π : SAdelicSchwartz F Sf →ₗ[ℂ] AdelicSchwartz F, IsLinearTopologicalEmbedding π ∧
      ∀ (f : SAdelicSchwartz F Sf) (x : AdeleRing (𝓞 F) F),
        (π f).eval x =
          f.eval (x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F))) *
            (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → x.2 v ∈ v.adicCompletionIntegers F
              then 1 else 0)) ∧
    (∀ f : AdelicSchwartz F, ∃ (Tf : Finset (HeightOneSpectrum (𝓞 F)))
        (f₀ : SAdelicSchwartz F Tf), ∀ x : AdeleRing (𝓞 F) F,
      f.eval x =
        f₀.eval (x.1, fun v : Tf => x.2 (v : HeightOneSpectrum (𝓞 F))) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Tf → x.2 v ∈ v.adicCompletionIntegers F
            then 1 else 0)) := by sorry

end MasulloGRH
