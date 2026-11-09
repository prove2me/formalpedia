-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_lemma_8_4
-- name    : MultiplierAssoc206.Resolution.lemma_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:23:52.866899+00:00
-- url     : https://prove2.me/theorems/de811b8a-4322-4bac-a3ba-f373f51ec5f7
-- title:
--   Locality of every wire and miter variable under $\rho$
-- statement:
--   Standing assumptions (§§5–8): $(\mathrm{Mul}_n)_n$ is a strip-local family; $H=(U,V,E)$ has $|U|=m+1$, $|V|=m$ and no isolated vertices; $i,j,k$ are index maps for $H$ with the properties of Lemma 7.3, strip width $g=\lceil\log_2(m+2)\rceil+2$ and bound $n_0$, and $n\ge n_0$; $\rho$ is the restriction of Definition 7.4 on $\mathsf{Assoc}_n$.
--
--   Under $\rho$ every variable $q$ of $\mathsf{Assoc}_n$ computes the Boolean function $\alpha\mapsto\bar\alpha(q)$ of the edge variables (Definition 8.1). Every wire of the four multipliers and every miter variable is constant, edge-local, or star-local at some vertex $w\in U\cup V$. Moreover, every wire of the inner multiplier $\mathbf{xy}$ computes a Boolean function of a single star $E(v)$, $v\in V$, and every wire of $\mathbf{yz}$ computes a Boolean function of a single star $E(u)$, $u\in U$.
--
--   Locality is what allows each wire to be replaced by one extension variable $Z_{w,f}$ of $\mathsf{SPM}(H)$.
--
--   Differences from the source:
--   - generalization: the maps i, j, k constructed in Lemma 7.3, and a graph of maximum degree at most a constant Δ → any maps with the properties (i)–(iii) of Lemma 7.3, for strip width g = ⌈log₂(m+2)⌉+2 and bound n₀ ≤ n; no degree bound; reason: the paper notes that the rest of the argument uses only the three properties (PDF p.17); the constructed maps have them, and every finite graph has some maximum degree
--   - encoding: a wire computes a Boolean function of a single star E(v) → the map α ↦ ᾱ(q) takes equal values on edge assignments that agree on E(v); reason: the semantic meaning of 'function of'; constants are functions of every star
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.19 (printed p.18), Lemma 8.4

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Rho

namespace MultiplierAssoc206.Resolution

/-- Lemma 8.4 (Locality), PDF p.19 (printed p.18). -/
theorem lemma_8_4 (Mul : (n : ℕ) → MulEncoding n) (hMul : StripLocal Mul)
    (m : ℕ) {U V : Type} [Fintype U] [Fintype V] (hU : Fintype.card U = m + 1)
    (hV : Fintype.card V = m) (E : Finset (U × V)) (hE : NoIsolated E)
    {n₀ : ℕ} (M : IndexMaps E (stripWidth m) n₀) (n : ℕ) (hn : n₀ ≤ n) :
    (∀ q : AVar Mul n, IsWireOrMiter q →
      IsConstFn (varFun Mul n M q) ∨ IsEdgeLocal (varFun Mul n M q) ∨
        ∃ w : U ⊕ V, IsStarLocalAt (varFun Mul n M q) w) ∧
    (∀ w : (Mul n).W, ∃ v : V, FunOf (varFun Mul n M (.xy w)) (star E (Sum.inr v))) ∧
    (∀ w : (Mul n).W, ∃ u : U, FunOf (varFun Mul n M (.yz w)) (star E (Sum.inl u))) := by sorry

end MultiplierAssoc206.Resolution
