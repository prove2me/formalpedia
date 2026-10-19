-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_concrete_slot_variance_le_av
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance_le_av
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:38:59.613265+00:00
-- url     : https://prove2.me/theorems/8acfc6c1-8c4d-4696-a148-e5fc7101384c
-- title:
--   Explicit variance bound for slot densities with the canonical number of chunks
-- statement:
--   Let $r\ge1$ and $d=(d_0,\dots,d_{r-1})\in\mathbb{N}^r$. Put $L_i=2d_i+1$, $L=\sum_{i}L_i$ and $P_i=\sum_{j<i}L_j$. Let $R\ge2$ be an integer and $q$ a prime with $2RL<q$, write $\mathbb{F}_q=\mathbb{Z}/q\mathbb{Z}$, and put
--   $$K=\Big\lfloor\frac{q-1}{2RL}\Big\rfloor .$$
--   A *slot choice* is a family $\omega=(\sigma_k,\epsilon_k)_{0\le k<K}$ of shifts $\sigma_k\in\{0,\dots,L-1\}$ and signs $\epsilon_k\in\{+1,-1\}$; $\Omega_K$ denotes the set of all slot choices. Row $i$ is *hit* at $u\in\mathbb{F}_q$ under $\omega$ if
--   $$u\equiv\epsilon_k\big(kRL+pL+\sigma_k+P_i+d_i+1\big)\pmod q\quad\text{for some }0\le k<K,\ 0\le p<R-1 .$$
--   Let $V$ be a finite vector space over $\mathbb{F}_q$ and $g_0,\dots,g_{r-1}:V\to\mathbb{F}_q$ linear forms such that every $g_i$ is surjective and $(g_i,g_j):V\to\mathbb{F}_q^2$ is surjective for all $i\neq j$. For a row $i$, $s\in\mathbb{F}_q$ and $\omega\in\Omega_K$, let $\rho_i^\omega(s)$ be the proportion of points $y$ of the hyperplane $\{g_i=s\}$ such that row $j$ is hit at $g_j(y)$ under $\omega$ for every $j\neq i$. Then for every row $i$
--   $$\operatorname{avg}_{\omega\in\Omega_K}\ \operatorname{avg}_{s\in\mathbb{F}_q}\Big(\rho_i^\omega(s)-(2L)^{-(r-1)}\Big)^2\ \le\ A_q,$$
--   where $\operatorname{avg}$ denotes a uniform average and
--   $$A_q=3\Big[2\Big((r-1)\Big(1-2(R-2)L\frac{K}{q}\Big)+\frac{2(r-1)^2(2RL+1)}{q}\Big)+(r-1)^2\Big(1-2(R-2)L\frac{K}{q}+\frac{2(R-2)L}{q}\Big)\Big].$$
--
--   This expresses the mean-square concentration of slot densities through an explicit function of $(r,L,R,q)$, whose limit as $q\to\infty$ is $6\big(2(r-1)+(r-1)^2\big)/R$. For large $R$ it supplies the variance hypothesis of the random matching step in the signed-slot packing.
--
--   **Formalization Note** $K$ is `chunkCount (2*R*L) q` and $A_q$ is `packingAV r L R q`; inside it $r-1$ is a truncated difference of natural numbers and $R-2$ a real difference. An index $i_0$ of type `Fin r` is an argument only to guarantee $r\ge1$. Slot choices are `SlotChoices d K`, the hit relation is `slotHit d R K q` and $\rho$ is `slotDensity`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SlotParameters.lean#L205-L250

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uV
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance_le_av {r q : ℕ} [Fact q.Prime]
    (d : Fin r → ℕ) (R : ℕ) (i₀ : Fin r) (hR : 2≤R)
    (hq' : 2*R*periodLength (oddLengths d)<q)
    {V : Type uV} [AddCommGroup V] [Module (ZMod q) V] [Fintype V] [DecidableEq V]
    (g : Fin r → V →ₗ[ZMod q] ZMod q)
    (hg : ∀ i, Function.Surjective (g i))
    (hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) (i : Fin r) :
    let K := chunkCount (2*R*periodLength (oddLengths d)) q
    avg (fun ω : SlotChoices d K ↦ avg (fun s : ZMod q ↦
      (slotDensity g (fun j t ↦ slotHit d R K q j ω t) i s-
        (1/(2*periodLength (oddLengths d) : ℝ))^(r-1))^2)) ≤
      packingAV r (periodLength (oddLengths d)) R q := by sorry
