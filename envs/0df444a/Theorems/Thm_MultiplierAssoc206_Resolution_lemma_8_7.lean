-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_lemma_8_7
-- name    : MultiplierAssoc206.Resolution.lemma_8_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:23:47.706273+00:00
-- url     : https://prove2.me/theorems/3040292b-cb16-4728-8ec9-a58bbf67cfee
-- title:
--   A refutation of $\mathsf{Assoc}_n$ yields a refutation of $\mathsf{SPM}(H)$ of constant-factor size
-- statement:
--   Let $(\mathrm{Mul}_n)_n$ be a strip-local family and $\Delta\in\mathbb N$. There is a constant $C$, depending only on the family and $\Delta$, such that the following holds for every $m$, every bipartite graph $H=(U,V,E)$ with $|U|=m+1$, $|V|=m$, maximum degree at most $\Delta$ and no isolated vertices, every choice of index maps for $H$ with the properties of Lemma 7.3 (strip width $g=\lceil\log_2(m+2)\rceil+2$, bound $n_0$), and every $n\ge n_0$: from every resolution refutation $\pi$ of $\mathsf{Assoc}_n$ one obtains a resolution refutation $\pi'$ of the star-local extension $\mathsf{SPM}(H)$ with
--   $$|\pi'|\le C\,|\pi|.$$
--
--   Combined with Theorem 5.6 this transfers the exponential lower bound to $\mathsf{Assoc}_n$.
--
--   Differences from the source:
--   - generalization: the maps of Lemma 7.3 and n ≥ n₀ → any maps with the properties (i)–(iii) of Lemma 7.3 and any n ≥ n₀; reason: the paper notes that the rest of the argument uses only the three properties (PDF p.17); the constructed maps have them
--   - encoding: with only a constant-factor increase in size → there is C, depending only on the family and on Δ, chosen before m, H, the maps, n and the refutation, with |π'| ≤ C |π|; reason: explicit form of 'constant factor'; the proof's constant depends on the clause-width bound of the family and on Δ
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.21 (printed p.20), Lemma 8.7

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Rho

namespace MultiplierAssoc206.Resolution

/-- Lemma 8.7 (Reduction from perfect matching), PDF p.21 (printed p.20): a refutation of
`Assoc_n` of size `s` yields a refutation of `SPM(H)` of size at most `C s`, where `C` depends
only on the encoding family and on the degree bound `Δ`. -/
theorem lemma_8_7 (Mul : (n : ℕ) → MulEncoding n) (hMul : StripLocal Mul) (Δ : ℕ) :
    ∃ Cst : ℕ, ∀ (m : ℕ) (U V : Type) [Fintype U] [Fintype V],
      Fintype.card U = m + 1 → Fintype.card V = m →
      ∀ E : Finset (U × V), MaxDegLE E Δ → NoIsolated E →
      ∀ (n₀ : ℕ) (_M : IndexMaps E (stripWidth m) n₀) (n : ℕ), n₀ ≤ n →
      ∀ π : List (Clause (AVar Mul n)), IsRefutation (Assoc Mul n) π →
        ∃ π' : List (Clause (ExtVar E)), IsRefutation (SPM E) π' ∧
          π'.length ≤ Cst * π.length := by sorry

end MultiplierAssoc206.Resolution
