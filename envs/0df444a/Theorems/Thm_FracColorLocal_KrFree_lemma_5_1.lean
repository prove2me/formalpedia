-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_lemma_5_1
-- name    : FracColorLocal.KrFree.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:12:14.390671+00:00
-- url     : https://prove2.me/theorems/1b9acaf8-0ec8-4c13-9c87-4771ba0df6ce
-- title:
--   Lemma 5.1 — structural dichotomy: T_G(w) ≤ C△D_θ, or sets A, B, p ≥ 1, ρ ∈ {θ_v} with (5.1)–(5.2)
-- statement:
--   Let $C_\triangle=2^{t_*}$ with $t_*=(100C_{\mathrm{loss}})^4$, $C_{\mathrm{loss}}=24(C_{\mathrm{ent}}+1)$, $C_{\mathrm{ent}}=20+12\cdot24^2$. For every finite graph $G$ with positive real weights $w,\theta$, one of the following holds:
--
--   (i) $T_G(w)\le C_\triangle D_\theta$;
--
--   (ii) there are sets $A,B\subseteq V(G)$, an integer $p\ge1$ and $\rho\in\{\theta_v:v\in V(G)\}$ such that
--   $$w(A),\,w(B)\le\rho2^p,\quad b(B)\le\rho^22^{2p},\qquad e_w(A,B)>24\big(p\,b(A)+\rho^22^{-p}\big).$$
--
--   If $G$ has no edges, including when it is empty, (i) holds.
--
--   The dichotomy, with Lemma 5.4, bounds the triangle weight at a maximizer of the potential (Corollary 5.5).
--
--   Differences from the source:
--   - generalization: "an absolute rational constant $C_\triangle\ge1$" → the explicit $C_\triangle=2^{t_*}$ fixed in §8; reason: §8 proves the lemma with this value, and the explicit statement implies the existential one ($2^{t_*}$ is a rational number $\ge1$); Corollary 5.5 then refers to the same constant.
--   - encoding: "$G$ has no edges" → `G = ⊥`; reason: same graphs.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 20 (PDF 21), Lemma 5.1; C△ fixed p. 33 (PDF 34), §8

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_FracColorLocal_KrFree_Constants
import Definitions.Def_FracColorLocal_KrFree_Dichotomy

open OAI.CliqueFreeIndependence.WeightedGraph

namespace FracColorLocal.KrFree

/-- Lemma 5.1 (structural dichotomy) with the explicit constant `C△ = 2^{t∗}` of §8:
(i) `T_G(w) ≤ C△ D_θ`, or (ii) there are `A, B`, an integer `p ≥ 1` and `ρ ∈ {θ_v}` with (5.1)
and (5.2); and (i) holds when `G` has no edges. -/
theorem lemma_5_1 {V : Type*} [Fintype V] (G : SimpleGraph V) (w θ : V → ℝ)
    (hw : ∀ v, 0 < w v) (hθ : ∀ v, 0 < θ v) :
    (triangleMass G w ≤ (Ctri : ℝ) * dTheta G w θ ∨
      ∃ (A B : Finset V) (p : ℕ) (v : V), 1 ≤ p ∧ IsWitness G w θ A B p (θ v)) ∧
    (G = ⊥ → triangleMass G w ≤ (Ctri : ℝ) * dTheta G w θ) := by sorry

end FracColorLocal.KrFree
