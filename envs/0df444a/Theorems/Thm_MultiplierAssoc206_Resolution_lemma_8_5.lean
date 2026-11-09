-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_lemma_8_5
-- name    : MultiplierAssoc206.Resolution.lemma_8_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:23:36.680808+00:00
-- url     : https://prove2.me/theorems/e447c7fd-e658-489b-b91c-ce3973d614a8
-- title:
--   Inner multipliers impose perfect matching
-- statement:
--   Standing assumptions (§§5–8): $(\mathrm{Mul}_n)_n$ is a strip-local family; $H=(U,V,E)$ has $|U|=m+1$, $|V|=m$ and no isolated vertices; $i,j,k$ are index maps for $H$ with the properties of Lemma 7.3, strip width $g=\lceil\log_2(m+2)\rceil+2$ and bound $n_0$, and $n\ge n_0$; $\rho$ is the restriction of Definition 7.4 on $\mathsf{Assoc}_n$.
--
--   For every assignment $\alpha$ of the edge variables, the propagated assignment $\bar\alpha$ satisfies every clause of $\mathbf{xy}{\restriction_\rho}$ (the inner multiplier $\mathrm{Mul}_n(x,y;xy)$ restricted by $\rho$) if and only if $\alpha$ sets exactly one edge variable of the star $E(v)$ to true for every $v\in V$. Symmetrically, $\bar\alpha$ satisfies $\mathbf{yz}{\restriction_\rho}$ if and only if $\alpha$ sets exactly one edge variable of $E(u)$ to true for every $u\in U$.
--
--   The statement holds for every $\alpha$, not only for perfect matchings, of which there are none.
--
--   Differences from the source:
--   - generalization: the maps i, j, k constructed in Lemma 7.3, and a graph of maximum degree at most a constant Δ → any maps with the properties (i)–(iii) of Lemma 7.3, for strip width g = ⌈log₂(m+2)⌉+2 and bound n₀ ≤ n; no degree bound; reason: the paper notes that the rest of the argument uses only the three properties (PDF p.17); the constructed maps have them, and every finite graph has some maximum degree
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.20 (printed p.19), Lemma 8.5

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Rho

namespace MultiplierAssoc206.Resolution

/-- Lemma 8.5 (Inner multipliers impose perfect matching), PDF p.20 (printed p.19). -/
theorem lemma_8_5 (Mul : (n : ℕ) → MulEncoding n) (hMul : StripLocal Mul)
    (m : ℕ) {U V : Type} [Fintype U] [Fintype V] (hU : Fintype.card U = m + 1)
    (hV : Fintype.card V = m) (E : Finset (U × V)) (hE : NoIsolated E)
    {n₀ : ℕ} (M : IndexMaps E (stripWidth m) n₀) (n : ℕ) (hn : n₀ ≤ n) (α : Edge E → Bool) :
    ((∀ C ∈ (innerXY Mul n).restrict (rho Mul n M), ClauseSat (propagate Mul n M α) C) ↔
      ∀ v : V, ExactlyOneAt α (Sum.inr v)) ∧
    ((∀ C ∈ (innerYZ Mul n).restrict (rho Mul n M), ClauseSat (propagate Mul n M α) C) ↔
      ∀ u : U, ExactlyOneAt α (Sum.inl u)) := by sorry

end MultiplierAssoc206.Resolution
