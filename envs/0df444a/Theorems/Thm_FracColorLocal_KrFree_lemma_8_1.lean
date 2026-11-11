-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_lemma_8_1
-- name    : FracColorLocal.KrFree.lemma_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:12:18.59239+00:00
-- url     : https://prove2.me/theorems/1a597c11-61d6-4ab9-bafc-b5d87f3f9fac
-- title:
--   Lemma 8.1 (Reduction step) — a witness with p ≤ 30t³, or deletion and splitting to Λ′/θ′ ≤ 2^{⌈√t⌉} with D_out ≤ D_in and T_out ≥ (1−δ(t))T_in − D_in/t
-- statement:
--   Let $t>t_*$ be an integer and let the current graph $G$ (finite, with positive vertex weights $w$ and parameters $\theta$) satisfy $\Lambda_v/\theta_v\le2^t$ at every vertex and $T_{\mathrm{in}}>2D_{\mathrm{in}}>0$, where $T_{\mathrm{in}}=T_G(w)$ and $D_{\mathrm{in}}=D_\theta$. Then either
--
--   - there are sets $A,B$, an integer $1\le p\le30t^3$ and $\rho$ a current vertex parameter ($\rho=\theta_v$) satisfying (5.1) and (5.2), or
--   - deletion and splitting produce a graph $G'$ (with projection $\sigma$, inherited weights $w'=w\circ\sigma$ and parameters $\theta'=\theta\circ\sigma$) in which, with $t'=\lceil\sqrt t\rceil$,
--   $$\Lambda'_v/\theta'_v\le2^{t'}\ \text{for every remaining vertex},\qquad D_{\mathrm{out}}\le D_{\mathrm{in}},\qquad T_{\mathrm{out}}\ge(1-\delta(t))T_{\mathrm{in}}-D_{\mathrm{in}}/t. \tag{8.2}$$
--
--   Iterating it brings the ratios $\Lambda_v/\theta_v$ down to an absolute constant while keeping most of the triangle weight, which proves Lemma 5.1.
--
--   Differences from the source:
--   - encoding: "deletion and splitting produce a graph" → there exist a finite vertex type $V'$, a graph $G'$ and $\sigma:V'\to V$ with `IsDeletionSplitting G G' σ`, and $\Lambda',T_{\mathrm{out}},D_{\mathrm{out}}$ computed in $G'$ with $w\circ\sigma$, $\theta\circ\sigma$; reason: these are the graphs reachable by deleting and splitting (isolated extra vertices, which the relation also allows, change none of the three quantities).
--   - reading: "sets and parameters satisfying (5.1) and (5.2), with $p\le30t^3$ and $\rho$ a current vertex parameter" → $A,B\subseteq V$, $1\le p\le30t^3$, $\rho=\theta_v$ for some $v$; reason: $p$ is the integer $p\ge1$ of Lemma 5.1(ii).
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 33 (PDF 34), Lemma 8.1, (8.1), (8.2)

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_FracColorLocal_KrFree_Constants
import Definitions.Def_FracColorLocal_KrFree_Dichotomy
import Definitions.Def_FracColorLocal_KrFree_Splitting

open OAI.CliqueFreeIndependence.WeightedGraph

namespace FracColorLocal.KrFree

/-- Lemma 8.1 (Reduction step). -/
theorem lemma_8_1 {V : Type} [Fintype V] (G : SimpleGraph V) (w θ : V → ℝ)
    (hw : ∀ v, 0 < w v) (hθ : ∀ v, 0 < θ v) (t : ℕ) (ht : tStar < t)
    (hΛ : ∀ v, neighborMass G w v / θ v ≤ (2 : ℝ) ^ t)
    (hTD : 2 * dTheta G w θ < triangleMass G w) (hD : 0 < dTheta G w θ) :
    (∃ (A B : Finset V) (p : ℕ) (v : V), 1 ≤ p ∧ p ≤ 30 * t ^ 3 ∧ IsWitness G w θ A B p (θ v)) ∨
    (∃ (V' : Type) (_ : Fintype V') (G' : SimpleGraph V') (σ : V' → V),
      IsDeletionSplitting G G' σ ∧
      (∀ v' : V', neighborMass G' (w ∘ σ) v' / θ (σ v') ≤ (2 : ℝ) ^ ⌈Real.sqrt t⌉₊) ∧
      dTheta G' (w ∘ σ) (θ ∘ σ) ≤ dTheta G w θ ∧
      (1 - deltaT t) * triangleMass G w - dTheta G w θ / t ≤ triangleMass G' (w ∘ σ)) := by sorry

end FracColorLocal.KrFree
