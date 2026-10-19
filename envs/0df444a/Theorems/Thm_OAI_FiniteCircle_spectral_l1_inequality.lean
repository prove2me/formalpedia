-- Prove2me | Theorems.Thm_OAI_FiniteCircle_spectral_l1_inequality
-- name    : OAI.FiniteCircle.spectral_l1_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:46:09.081987+00:00
-- url     : https://prove2.me/theorems/8761f4f0-8da1-44f2-ac86-d46eda1335c2
-- title:
--   Character inequalities transfer to $\ell^1$-valued maps on finite abelian groups
-- statement:
--   Let $G$ be a finite abelian group, $T$ a finite set, $w\in G$, $a:T\to G$ and $q:T\to\mathbb{R}$ (no sign condition on $q$). An additive character of $G$ is a map $\chi:G\to\mathbb{C}$ with $\chi(0)=1$ and $\chi(x+y)=\chi(x)\chi(y)$. Let $\ell^1=\ell^1(\mathbb{N})$ be the space of absolutely summable real sequences with norm $\|u\|_1=\sum_{i\in\mathbb{N}}|u_i|$, and let $\mathbb{E}_{x\in G}$ denote the uniform average over $G$.
--
--   Assume that every additive character $\chi$ of $G$ satisfies
--
--   $$
--   |1-\chi(w)|^2\le\sum_{t\in T}q_t\,|1-\chi(a_t)|^2 .
--   $$
--
--   Then every map $f:G\to\ell^1$ satisfies
--
--   $$
--   \mathbb{E}_{x\in G}\,\|f(x+w)-f(x)\|_1\le\sum_{t\in T}q_t\;\mathbb{E}_{x\in G}\,\|f(x+a_t)-f(x)\|_1 .
--   $$
--
--   So a Poincaré-type inequality that holds on the Fourier side, character by character, automatically holds for the average displacements of arbitrary $\ell^1$-valued maps. It is the bridge between Fourier analysis on finite abelian groups and lower bounds for the distortion of embeddings into $\ell^1$.
--
--   **Formalization Note** $\ell^1$ is `RealL1`, the Mathlib space `lp (fun _ : ℕ => ℝ) 1`; characters are `AddChar G ℂ`, $|z|^2$ is `Complex.normSq z`, and the averages are Mathlib's expectation notation over `Finset.univ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Fourier.lean#L264-L288

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped BigOperators ComplexConjugate
open RCLike Module
open scoped BigOperators

theorem OAI.FiniteCircle.spectral_l1_inequality {G T : Type*} [AddCommGroup G] [Fintype G] [Fintype T]
    (w : G) (a : T → G) (q : T → ℝ)
    (hs : ∀ χ : AddChar G ℂ, Complex.normSq (1-χ w) ≤
      ∑ t, q t * Complex.normSq (1-χ (a t))) (f : G → RealL1) :
    (𝔼 x, ‖f (x+w)-f x‖) ≤ ∑ t, q t * (𝔼 x, ‖f (x+a t)-f x‖) := by sorry
