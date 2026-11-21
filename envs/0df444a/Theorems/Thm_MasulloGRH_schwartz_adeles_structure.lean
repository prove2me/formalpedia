-- Prove2me | Theorems.Thm_MasulloGRH_schwartz_adeles_structure
-- name    : MasulloGRH.schwartz_adeles_structure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T03:47:29.202595+00:00
-- url     : https://prove2.me/theorems/1930da0b-bd5f-4689-acc8-a4d636e368b1
-- title:
--   Lemma 2.1.3.2(1) — $\mathcal S(\mathbb A_F^f)$ and $\mathcal S(\mathbb A_F)$ are strict inductive limits of nuclear Fréchet spaces
-- statement:
--   Let $F$ be a number field, $\mathbb A_F$ its adele ring and $\mathbb A_F^f$ its ring of finite adeles, and let $\mathcal S(\mathbb A_F)$ and $\mathcal S(\mathbb A_F^f)$ be the Schwartz–Bruhat spaces of their additive groups.
--
--   For $E=\mathcal S(\mathbb A_F)$ and for $E=\mathcal S(\mathbb A_F^f)$:
--
--   1. $E$ is a strict locally convex inductive limit of a sequence of nuclear Fréchet spaces; in particular it is a strict LF-space.
--   2. $E$ is Hausdorff, complete, nuclear and Montel.
--   3. The strong dual $E'_\beta$ is complete, nuclear and Montel.
--
--   Moreover, the strong dual $\mathcal S(\mathbb A_F^f)'_\beta$ is a nuclear Fréchet space.
--
--   These properties allow the draft to form quotients, strong duals and topological tensor products of spaces of adelic Schwartz–Bruhat functions.
--
--   **Formalization Note** This is part (1) of the source lemma.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.1.3, Lemma 2.1.3.2, part (1), p. 68

import Definitions.Def_MasulloGRH_AdelicTheta

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem schwartz_adeles_structure (F : Type*) [Field F] [NumberField F] :
    (IsStrictLFOfNuclearFrechet (AdelicSchwartz F) ∧ IsStrictLF (AdelicSchwartz F) ∧
      IsHLCS (AdelicSchwartz F) ∧ IsCompleteTVS (AdelicSchwartz F) ∧
      IsNuclear (AdelicSchwartz F) ∧ IsMontel (AdelicSchwartz F) ∧
      IsCompleteTVS (StrongDual ℂ (AdelicSchwartz F)) ∧
      IsNuclear (StrongDual ℂ (AdelicSchwartz F)) ∧ IsMontel (StrongDual ℂ (AdelicSchwartz F))) ∧
    (IsStrictLFOfNuclearFrechet (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))) ∧
      IsStrictLF (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))) ∧
      IsHLCS (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))) ∧
      IsCompleteTVS (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))) ∧
      IsNuclear (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))) ∧
      IsMontel (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))) ∧
      IsCompleteTVS (StrongDual ℂ (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F)))) ∧
      IsNuclear (StrongDual ℂ (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F)))) ∧
      IsMontel (StrongDual ℂ (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F)))) ∧
      IsFrechet (StrongDual ℂ (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))))) := by sorry

end MasulloGRH
