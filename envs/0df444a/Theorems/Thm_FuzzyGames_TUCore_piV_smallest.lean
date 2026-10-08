-- Prove2me | Theorems.Thm_FuzzyGames_TUCore_piV_smallest
-- name    : FuzzyGames.TUCore.piV_smallest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:32.985288+00:00
-- url     : https://prove2.me/theorems/96b297c8-da72-425f-9309-f0955b0ebd1c
-- title:
--   §6 (2) — $\pi v$ is the smallest concave positively homogeneous function larger than $v$
-- statement:
--   Let $\mathscr C$ be a family of nonempty coalitions containing $N$ and every singleton, and let $v:\mathscr C\to\mathbb R$. Define, for $\tau\in\mathbb R^n_+$,
--   $$\pi v(\tau)=\sup_{m\in\mathscr C(\tau)}\ \sum_{A\in\mathscr C}m(A)\,v(A).$$
--   Then $\pi v$ is the smallest concave positively homogeneous function on $\mathbb R^n_+$ larger than the discrete function $A\mapsto v(A)$:
--
--   1. $\pi v$ is concave on $\mathbb R^n_+$, and $\pi v(t\tau)=t\,\pi v(\tau)$ for all $t>0$, $\tau\in\mathbb R^n_+$;
--   2. $\pi v(\tau^A)\ge v(A)$ for every $A\in\mathscr C$;
--   3. if $w:\mathbb R^n_+\to\mathbb R$ is concave, satisfies $w(t\tau)=t\,w(\tau)$ for $t>0$, $\tau\in\mathbb R^n_+$, and $w(\tau^A)\ge v(A)$ for every $A\in\mathscr C$, then $\pi v(\tau)\le w(\tau)$ for every $\tau\in\mathbb R^n_+$.
--
--   The function $\pi v$ is the fuzzy game associated with the usual game $v$; Proposition 2.1 applies to it.
--
--   **Formalization Note** "Larger than the discrete function $v$" is read as $\pi v(\tau^A)\ge v(A)$ for $A\in\mathscr C$. Concavity and homogeneity are on the orthant $\mathbb R^n_+$, where $\pi v$ is a finite real supremum (see the definition file); values off the orthant are not used. The printed $v(\mathscr C)$ in (2) is read as $v(A)$.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §6, p. 8, sentence before (2), and (2)–(4)

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

namespace FuzzyGames.TUCore

theorem piV_smallest {n : ℕ} (𝒞 : FuzzyGames.NTUCore.CoalFamily n) (v : Finset (Fin n) → ℝ) :
    (ConcaveOn ℝ (Set.Ici (0 : Fin n → ℝ)) (piV 𝒞 v) ∧
      ∀ t : ℝ, 0 < t → ∀ τ : Fin n → ℝ, 0 ≤ τ → piV 𝒞 v (t • τ) = t * piV 𝒞 v τ) ∧
    (∀ A ∈ 𝒞.C, piV 𝒞 v (FuzzyGames.NTUCore.coal A) ≥ v A) ∧
    (∀ w : (Fin n → ℝ) → ℝ, ConcaveOn ℝ (Set.Ici (0 : Fin n → ℝ)) w →
      (∀ t : ℝ, 0 < t → ∀ τ : Fin n → ℝ, 0 ≤ τ → w (t • τ) = t * w τ) →
      (∀ A ∈ 𝒞.C, w (FuzzyGames.NTUCore.coal A) ≥ v A) →
      ∀ τ : Fin n → ℝ, 0 ≤ τ → piV 𝒞 v τ ≤ w τ) := by sorry

end FuzzyGames.TUCore
