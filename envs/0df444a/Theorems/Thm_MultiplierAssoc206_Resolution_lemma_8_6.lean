-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_lemma_8_6
-- name    : MultiplierAssoc206.Resolution.lemma_8_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:24:18.641109+00:00
-- url     : https://prove2.me/theorems/f43b65ad-e445-4372-95be-9cfc454ad8b3
-- title:
--   Local soundness
-- statement:
--   Standing assumptions (§§5–8): $(\mathrm{Mul}_n)_n$ is a strip-local family; $H=(U,V,E)$ has $|U|=m+1$, $|V|=m$ and no isolated vertices; $i,j,k$ are index maps for $H$ with the properties of Lemma 7.3, strip width $g=\lceil\log_2(m+2)\rceil+2$ and bound $n_0$, and $n\ge n_0$; $\rho$ is the restriction of Definition 7.4 on $\mathsf{Assoc}_n$.
--
--   Let $C$ be a clause of $\mathsf{Assoc}_n{\restriction_\rho}$ and $\alpha$ an assignment of the edge variables that satisfies $\mathrm{ExactOne}(X_{E(w)})$ — sets exactly one edge of $E(w)$ to true — for every vertex $w$ in the support $\mathrm{supp}(C)$ (Definition 8.3). Then the propagated assignment $\bar\alpha$ satisfies $C$.
--
--   The lemma shows that each restricted clause follows from the clauses of $\mathsf{SPM}(H)$ of a bounded number of stars.
--
--   Differences from the source:
--   - generalization: the maps i, j, k constructed in Lemma 7.3, and a graph of maximum degree at most a constant Δ → any maps with the properties (i)–(iii) of Lemma 7.3, for strip width g = ⌈log₂(m+2)⌉+2 and bound n₀ ≤ n; no degree bound; reason: the paper notes that the rest of the argument uses only the three properties (PDF p.17); the constructed maps have them, and every finite graph has some maximum degree
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.21 (printed p.20), Lemma 8.6

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Rho

namespace MultiplierAssoc206.Resolution

/-- Lemma 8.6 (Local soundness), PDF p.21 (printed p.20). -/
theorem lemma_8_6 (Mul : (n : ℕ) → MulEncoding n) (hMul : StripLocal Mul)
    (m : ℕ) {U V : Type} [Fintype U] [Fintype V] (hU : Fintype.card U = m + 1)
    (hV : Fintype.card V = m) (E : Finset (U × V)) (hE : NoIsolated E)
    {n₀ : ℕ} (M : IndexMaps E (stripWidth m) n₀) (n : ℕ) (hn : n₀ ≤ n) (C : Clause (AVar Mul n))
    (hC : C ∈ (Assoc Mul n).restrict (rho Mul n M)) (α : Edge E → Bool)
    (hα : ∀ w ∈ supp Mul n M C, ExactlyOneAt α w) :
    ClauseSat (propagate Mul n M α) C := by sorry

end MultiplierAssoc206.Resolution
