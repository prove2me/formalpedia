-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_lemma_7_6
-- name    : MultiplierAssoc206.Resolution.lemma_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:23:35.965956+00:00
-- url     : https://prove2.me/theorems/0d899d22-4e04-48f6-a7d4-09166d291ebf
-- title:
--   $\rho$ forces disagreement at column $K$
-- statement:
--   Standing assumptions (§§5–8): $(\mathrm{Mul}_n)_n$ is a strip-local family; $H=(U,V,E)$ has $|U|=m+1$, $|V|=m$ and no isolated vertices; $i,j,k$ are index maps for $H$ with the properties of Lemma 7.3, strip width $g=\lceil\log_2(m+2)\rceil+2$ and bound $n_0$, and $n\ge n_0$; $\rho$ is the restriction of Definition 7.4 on $\mathsf{Assoc}_n$.
--
--   Under $\rho$, the outer multiplier strips at base $K$ are forced to output the binary representation of $m$ in $(\mathbf{xy})\mathbf z$ and of $m+1$ in $\mathbf x(\mathbf{yz})$: for every $t<g$ with $K+t<4n$ and every input assignment of $(\mathbf{xy})\mathbf z$ consistent with $\rho$,
--   $$\big((\mathbf{xy})\mathbf z\big)_{K+t}=\mathrm{bit}_t(m),$$
--   and for every input assignment of $\mathbf x(\mathbf{yz})$ consistent with $\rho$, $\big(\mathbf x(\mathbf{yz})\big)_{K+t}=\mathrm{bit}_t(m+1)$. In particular the output bits at column $K$ of the two outer multipliers disagree under any two such input assignments.
--
--   This is why $\rho$ may set $e_K=1$, satisfying the long miter clause.
--
--   Differences from the source:
--   - generalization: the maps i, j, k constructed in Lemma 7.3, and a graph of maximum degree at most a constant Δ → any maps with the properties (i)–(iii) of Lemma 7.3, for strip width g = ⌈log₂(m+2)⌉+2 and bound n₀ ≤ n; no degree bound; reason: the paper notes that the rest of the argument uses only the three properties (PDF p.17); the constructed maps have them, and every finite graph has some maximum degree
--   - encoding: the strips at base K are forced to output m and m + 1; the output bits at column K disagree → for every input assignment of the outer multiplier consistent with the input restriction induced by ρ, the function of output wire K + t (t < g, K + t < 4n) is bit t of m, resp. m + 1; for any two such assignments of the two outer multipliers the functions of output wire K differ; reason: exactness makes each output wire equal to its function; K < n₀ ≤ n, so the base bit always exists
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.19 (printed p.18), Lemma 7.6

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Rho

namespace MultiplierAssoc206.Resolution

/-- Lemma 7.6 (ρ forces disagreement), PDF p.19 (printed p.18): under every input assignment
consistent with ρ, the strip at base `K` outputs `m` in binary in `(xy)z` and `m + 1` in
`x(yz)`; in particular the output bits at column `K` disagree. -/
theorem lemma_7_6 (Mul : (n : ℕ) → MulEncoding n) (hMul : StripLocal Mul)
    (m : ℕ) {U V : Type} [Fintype U] [Fintype V] (hU : Fintype.card U = m + 1)
    (hV : Fintype.card V = m) (E : Finset (U × V)) (hE : NoIsolated E)
    {n₀ : ℕ} (M : IndexMaps E (stripWidth m) n₀) (n : ℕ) (hn : n₀ ≤ n) :
    (∀ t : ℕ, t < stripWidth m → ∀ (ht : M.K + t < 2 * (2 * n)) (X Z : Fin (2 * n) → Bool),
      ConsistentInputs (restrXYZ Mul n M) X Z →
        (Mul (2 * n)).fn ((Mul (2 * n)).out ⟨M.K + t, ht⟩) X Z = Nat.testBit m t) ∧
    (∀ t : ℕ, t < stripWidth m → ∀ (ht : M.K + t < 2 * (2 * n)) (X Y : Fin (2 * n) → Bool),
      ConsistentInputs (restrXYZ' Mul n M) X Y →
        (Mul (2 * n)).fn ((Mul (2 * n)).out ⟨M.K + t, ht⟩) X Y = Nat.testBit (m + 1) t) ∧
    (∀ (hK : M.K < 2 * (2 * n)) (X Z X' Y : Fin (2 * n) → Bool),
      ConsistentInputs (restrXYZ Mul n M) X Z → ConsistentInputs (restrXYZ' Mul n M) X' Y →
        (Mul (2 * n)).fn ((Mul (2 * n)).out ⟨M.K, hK⟩) X Z ≠
          (Mul (2 * n)).fn ((Mul (2 * n)).out ⟨M.K, hK⟩) X' Y) := by sorry

end MultiplierAssoc206.Resolution
