-- Prove2me | Theorems.Thm_NodeStableProj_Main_claim_3_8
-- name    : NodeStableProj.Main.claim_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:59:05.029813+00:00
-- url     : https://prove2.me/theorems/ad4cb655-ff83-4788-bbcf-2d1fca4d6680
-- title:
--   Claim 3.8 — for ω ∈ Good_{v*}, P^0_ω and P^1_ω are the two outputs of a concurrent D̂-sparse composition of the n − 1 SVT detectors
-- statement:
--   Let $0<D<\hat D$ be integers, $\tilde\varepsilon>0$, $\tau=(D+\hat D)/2$ and $k=(\hat D-D)/2$. Let $G,G'$ be fixed-vertex node-neighbouring graphs on a common vertex set $V$ with $|V|=n$ and differing node $v^*$, with $v^*$ isolated in $G$. Let $\omega$ be a noise vector for $t(v^*)$ in $\mathrm{Good}_{v^*}$, i.e. $|\omega(0)|<k/2$ and $|\omega(\ell)|<k/2$ for $\ell\in[n-1]$. Then there is an adversary $\mathcal A$ such that $\mathcal A,\mathcal I$ define a concurrent $\hat D$-sparse composition of the $n-1$ SVT detector mechanisms $t(u)$, $u\in V\setminus\{v^*\}$ (threshold $\tau$, parameter $\tilde\varepsilon$), and for both $b\in\{0,1\}$
--   $$\mathcal A*\mathcal I[b]*\{t(u)\}_{u\ne v^*}\ \sim\ P^b_\omega,$$
--   where $P^0_\omega$ is the law of $\tilde{\mathcal P}_{D,\hat D,\tilde\varepsilon}(G)_{-v^*}$ and $P^1_\omega$ that of $\tilde{\mathcal P}_{D,\hat D,\tilde\varepsilon}(G')_{-v^*}$, in both cases with $t(v^*)$'s noise fixed to $\omega$.
--
--   This reduces the stability of the projection to Proposition 3.7.
--
--   Differences from the source:
--   - reading: "every pair of node-neighboring graphs G, G' that differ on node v*" → fixed-vertex node-neighbours with v* isolated in G; reason: the proof fixes this orientation "without loss of generality" (p. 14) before defining P^0_ω, P^1_ω; the other orientation is the same statement with the roles of b swapped
--   - generalization: G, G' ∈ G^n (vertex set [n]) → any common vertex set V ⊂ ℕ with |V| = n; reason: labels are identities and Algorithm 1 uses only their order; V = [n] is a special case
--   - encoding: the detectors' Laplace noises → drawn from uniform tapes by the inverse distribution function of Lap(b) (svtMechanism), while P^b_ω uses the Laplace product law; reason: same laws
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), pp. 16–17, Claim 3.8

import Mathlib
import Definitions.Def_NodeStableProj_Main_Projection
import Definitions.Def_NodeStableProj_Main_Concurrent

open MeasureTheory

namespace NodeStableProj.Main

/-- Claim 3.8, pp. 16–17: for fixed-vertex node-neighbouring `G, G'` with differing node `v*`
isolated in `G`, and every `ω ∈ Good_{v*}`, there is an adversary `A` such that `A, I` define a
concurrent `D̂`-sparse composition of the `n − 1` SVT detectors `t(u)`, `u ≠ v*` (threshold
`τ = (D + D̂)/2`, parameter `ε̃`), whose output law with identifier bit `b` is `P^b_ω`
(`b = 0`: `P̃(G)_{−v*}`; `b = 1`: `P̃(G')_{−v*}`). -/
theorem claim_3_8 (D Dhat : ℕ) (εt : ℝ) (hD : 0 < D) (hDD : D < Dhat) (hεt : 0 < εt)
    (G G' : Graph) (vstar : ℕ) (hGG' : FixedVertexNeighbors G G' vstar)
    (hiso : G.deg vstar = 0) (ω : ℕ → ℝ)
    (hω : Good (((Dhat : ℝ) - D) / 2) G.V.card ω) :
    ∃ A : Adversary ↥(G.V.erase vstar) unitInterval Bool Graph,
      IsSparseComposition (fun _ => svtMechanism (((D : ℝ) + Dhat) / 2) εt) A Dhat ∧
      compositionLaw (fun _ => svtMechanism (((D : ℝ) + Dhat) / 2) εt) A false =
        projTildeLawFixing D Dhat εt G vstar ω ∧
      compositionLaw (fun _ => svtMechanism (((D : ℝ) + Dhat) / 2) εt) A true =
        projTildeLawFixing D Dhat εt G' vstar ω := by sorry

end NodeStableProj.Main
