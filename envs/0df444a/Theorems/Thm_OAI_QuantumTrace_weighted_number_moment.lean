-- Prove2me | Theorems.Thm_OAI_QuantumTrace_weighted_number_moment
-- name    : OAI.QuantumTrace.weighted_number_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:02:41.949397+00:00
-- url     : https://prove2.me/theorems/d374ad81-55c7-4976-a011-7bcf4d94574d
-- title:
--   Weighted diagonal moments of a diagonalized positive operator are summable
-- statement:
--   Let $\iota$ and $J$ be index sets, let $\ell^2(\iota)$ have standard basis $(e_i)_{i\in\iota}$, and let $(b_j)_{j\in J}$ be a Hilbert basis of $\ell^2(\iota)$ with coordinates $b_j(i)$. Let $T$ be a bounded operator on $\ell^2(\iota)$ with $Tb_j=p_jb_j$ for real numbers $p_j\ge 0$. Let $w:\iota\to\mathbb{R}$ be nonnegative weights and suppose that for each $j$ the series $\sum_iw_i|b_j(i)|^2$ converges with sum $\nu_j$, and that $\sum_jp_j\nu_j$ converges. Then the weighted diagonal series of $T$ converges:
--   $$\sum_{i\in\iota}w_i\,\operatorname{Re}\langle e_i,T\,e_i\rangle<\infty .$$
--
--   Here $\nu_j$ is the $w$-moment of the eigenvector $b_j$, and $\langle e_i,Te_i\rangle=\sum_jp_j|b_j(i)|^2$ is the diagonal of $T$ in the standard basis. The theorem says that if the eigenvalue-weighted moments of the eigenvectors are summable, then the state $T$ has a finite $w$-moment. With $w_i$ a power of the photon number, this yields finite photon-number moments for a state built from an eigenbasis.
--
--   **Formalization Note** The standard basis is `sequenceBasis ι`, and the conclusion is `Summable` of the real-valued family.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L1499-L1526

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
variable {ι J : Type*}

theorem OAI.QuantumTrace.weighted_number_moment (b : HilbertBasis J ℂ (SequenceHilbert ι))
    (T : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (he : ∀ j, T (b j) = (p j : ℂ) • b j)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ν : J → ℝ)
    (hrow : ∀ j, HasSum (fun i => w i*‖b j i‖^2) (ν j))
    (hs : Summable (fun j => p j*ν j)) :
    Summable (fun i => w i*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re) := by sorry
