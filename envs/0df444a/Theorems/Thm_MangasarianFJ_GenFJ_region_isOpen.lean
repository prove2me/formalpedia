-- Prove2me | Theorems.Thm_MangasarianFJ_GenFJ_region_isOpen
-- name    : MangasarianFJ.GenFJ.region_isOpen
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:41:14.460826+00:00
-- url     : https://prove2.me/theorems/97ce1e3a-d287-4c42-ad1e-54b4f8f640ab
-- title:
--   §2, proof of the generalized Fritz John conditions, p. 41, (2.14) — D = {x : g_i(x) < 0, i ∈ M − M̄} is open
-- statement:
--   Let $g_1,\dots,g_m:E^n\to\mathbb R$ be continuous and $\bar x\in E^n$. With the active set $\bar M=\{i\in M: g_i(\bar x)=0\}$ (2.13), the set
--
--   $$
--   D=\{x\in E^n : g_i(x)<0,\ i\in M\setminus\bar M\} \tag{2.14}
--   $$
--
--   is open in $E^n$.
--
--   This is the first step of the proof of the main result: $D$ is the open set on which Lemma 2 is applied.
--
--   **Formalization Note** Only continuity of the $g_i$ is assumed, which is what the page uses ("Since $M-\bar M$ is finite, and $g_i(x)$ are continuous"); the objective, the equalities and the $C^1$ hypothesis of §1 play no role here and are dropped, which makes the statement stronger.
-- source:
--   Mangasarian and Fromovitz, The Fritz John necessary optimality conditions in the presence of equality and inequality constraints, J. Math. Anal. Appl. 17 (1967), p. 41, §2, proof of the generalized Fritz John conditions, (2.13)–(2.14)

import Mathlib
import Definitions.Def_MangasarianFJ_GenFJ_Setting

namespace MangasarianFJ.GenFJ
theorem region_isOpen {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ∀ i, Continuous (g i)) (xbar : EuclideanSpace ℝ (Fin n)) :
    IsOpen (region g xbar) := by sorry
end MangasarianFJ.GenFJ
