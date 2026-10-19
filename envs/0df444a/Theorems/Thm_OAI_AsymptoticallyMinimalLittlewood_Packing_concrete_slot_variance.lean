-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_concrete_slot_variance
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:35:52.597397+00:00
-- url     : https://prove2.me/theorems/82219794-ebb0-44cb-9aa6-26b920abbebd
-- title:
--   Second-moment bound for slot densities in the signed-slot construction modulo a prime
-- statement:
--   Let $r\ge1$ and $d=(d_0,\dots,d_{r-1})\in\mathbb{N}^r$. Put $L_i=2d_i+1$, $L=\sum_{i}L_i$ and $P_i=\sum_{j<i}L_j$. Fix integers $R,K\ge0$ and a prime $q$, and write $\mathbb{F}_q=\mathbb{Z}/q\mathbb{Z}$. Differences of natural numbers below ($r-1$, $R-1$, $R-2$) are truncated at $0$.
--
--   - A *slot choice* is a family $\omega=(\sigma_k,\epsilon_k)_{0\le k<K}$ of shifts $\sigma_k\in\{0,\dots,L-1\}$ and signs $\epsilon_k\in\{+1,-1\}$; let $\Omega_K$ be the set of all slot choices, so $|\Omega_K|=(2L)^K$.
--   - The *centre* of slot $i$ in period $p$ of chunk $k$ with shift $\sigma$ is the integer $c_{k,p,i}(\sigma)=kRL+pL+\sigma+P_i+d_i+1$.
--   - Row $i$ is *hit* at $u\in\mathbb{F}_q$ under $\omega$ if $u\equiv\epsilon_k\,c_{k,p,i}(\sigma_k)\pmod q$ for some $0\le k<K$ and some $0\le p<R-1$.
--   - The *catalog* is $\mathcal{C}=\{\pm(kRL+L+1+t)\bmod q:\ 0\le k<K,\ 0\le t<(R-2)L\}\subseteq\mathbb{F}_q$, and the *short residues* are $S=\{x\bmod q:\ x\in\mathbb{Z},\ |x|\le RL\}$.
--
--   Let $V$ be a finite vector space over $\mathbb{F}_q$ and $g_0,\dots,g_{r-1}:V\to\mathbb{F}_q$ linear forms. For a row $i$, a value $s\in\mathbb{F}_q$ and $\omega\in\Omega_K$, the *slot density* $\rho_i^\omega(s)$ is the proportion of points $y$ of the hyperplane $\{g_i=s\}$ such that, for every row $j\neq i$, row $j$ is hit at $g_j(y)$ under $\omega$. We write $\operatorname{avg}$ for uniform averages over finite sets.
--
--   Assume $K>0$, $2KRL<q$, every $g_i$ is surjective and $(g_i,g_j):V\to\mathbb{F}_q^2$ is surjective for all $i\neq j$. Then for every row $i$
--   $$\operatorname{avg}_{\omega\in\Omega_K}\ \operatorname{avg}_{s\in\mathbb{F}_q}\Big(\rho_i^\omega(s)-(2L)^{-(r-1)}\Big)^2\ \le\ 3\left[2\left(\frac{(r-1)(q-|\mathcal{C}|)}{q}+\frac{2(r-1)^2|S|}{q}\right)+\frac{(r-1)^2\big(q-|\mathcal{C}|+2(R-2)L\big)}{q}\right].$$
--
--   The value $(2L)^{-(r-1)}$ is the probability that $r-1$ given rows are all hit when each hit event is decided by an independent uniform choice of one of the $2L$ shift-sign pairs. The right-hand side is small when the catalog covers most of $\mathbb{F}_q$ and $RL$ is small compared with $q$. This is the mean-square concentration of slot densities for the periodic signed-slot pattern, which feeds the degree concentration of the random slot hypergraph used to build the interval packing.
--
--   **Formalization Note** An index $i_0$ of type `Fin r` is an argument only to guarantee $r\ge1$ (hence $L>0$). Slot choices form the type `SlotChoices d K` of maps `Fin K → Fin L × Bool` (the Boolean `true` meaning the sign $+1$), the hit relation is `slotHit d R K q`, $\mathcal{C}$ is `catalogSet d R K q`, $S$ is `shortResidues q (R*L)` and $\rho$ is `slotDensity`. The difference $q-|\mathcal{C}|$ is taken in the reals in the first term and in the natural numbers in the last term; the two agree because $|\mathcal{C}|\le q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SlotGraph.lean#L256-L285

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

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uI uK uV uJ
open scoped BigOperators
open Finset Nibble
attribute [local instance] Classical.propDecidable

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance {r q : ℕ} [Fact q.Prime] (d : Fin r → ℕ)
    (R K : ℕ) (i₀ : Fin r) (hK : 0<K)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q)
    {V : Type uV} [AddCommGroup V] [Module (ZMod q) V] [Fintype V] [DecidableEq V]
    (g : Fin r → V →ₗ[ZMod q] ZMod q)
    (hg : ∀ i, Function.Surjective (g i))
    (hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) (i : Fin r) :
    avg (fun ω : SlotChoices d K ↦ avg (fun s : ZMod q ↦
      (slotDensity g (fun j t ↦ slotHit d R K q j ω t) i s-
        (1/(2*periodLength (oddLengths d) : ℝ))^(r-1))^2)) ≤
      3*(2*((r-1 : ℕ)*(q-(catalogSet d R K q).card : ℝ)/q+
          2*((r-1 : ℕ) : ℝ)^2*(shortResidues q (R*periodLength (oddLengths d))).card/q)+
        ((r-1 : ℕ) : ℝ)^2*
          (((q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) : ℕ) : ℝ)/q) := by sorry
