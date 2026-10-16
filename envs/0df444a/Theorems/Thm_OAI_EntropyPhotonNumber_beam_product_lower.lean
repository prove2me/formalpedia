-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_beam_product_lower
-- name    : OAI.EntropyPhotonNumber.beam_product_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:53:03.278996+00:00
-- url     : https://prove2.me/theorems/bfc6477f-bee4-43d7-adec-7078a30162c3
-- title:
--   Mode-wise lowering recurrences lift to products over modes
-- statement:
--   Let $n\in\mathbb{N}$ and fix a mode $j\in\{1,\dots,n\}$. For each mode $i$ let $f_i:\mathbb{N}^4\to\mathbb{R}$ be a real function, and let $k,e,a,b\in\mathbb{N}^n$ be multi-indices and $u,c,s\in\mathbb{R}$. For a multi-index $x$ write $x+\delta_j$ and $x-\delta_j$ for $x$ with its $j$-th coordinate replaced by $x_j+1$ and by $x_j-1$ respectively (truncated subtraction, so $0-1=0$). Suppose the single-mode recurrence
--   $$u\,f_j(k_j+1,e_j,a_j,b_j)=c\,f_j(k_j,e_j,a_j-1,b_j)+s\,f_j(k_j,e_j,a_j,b_j-1)$$
--   holds at mode $j$. Then the same recurrence holds for the products over all modes:
--   $$u\prod_{i=1}^n f_i\big((k+\delta_j)_i,e_i,a_i,b_i\big)=c\prod_{i=1}^n f_i\big(k_i,e_i,(a-\delta_j)_i,b_i\big)+s\prod_{i=1}^n f_i\big(k_i,e_i,a_i,(b-\delta_j)_i\big).$$
--
--   This lets one-mode identities for beam-splitter coefficients, such as the recursions obtained by lowering one photon number, be transferred to the multimode coefficients, which are products of one-mode coefficients over the modes.
--
--   **Formalization Note** Multi-indices are functions $\mathrm{Fin}\,n\to\mathbb{N}$ and the modified indices are written with `Function.update`. The subtraction $a_j-1$ is natural-number subtraction, so it equals $0$ when $a_j=0$; the statement holds verbatim with this convention.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Fock/Beam.lean#L848-L879

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam

open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open FischerBeam

theorem OAI.EntropyPhotonNumber.beam_product_lower {n : ℕ} (j : Fin n) (f : Fin n → ℕ → ℕ → ℕ → ℕ → ℝ)
    (k e a b : NumberIndex n) (u c s : ℝ)
    (h : u*f j (k j+1) (e j) (a j) (b j) =
      c*f j (k j) (e j) (a j-1) (b j)+s*f j (k j) (e j) (a j) (b j-1)) :
    u*(∏ i, f i (Function.update k j (k j+1) i) (e i) (a i) (b i)) =
      c*(∏ i, f i (k i) (e i) (Function.update a j (a j-1) i) (b i))+
      s*(∏ i, f i (k i) (e i) (a i) (Function.update b j (b j-1) i)) := by sorry
