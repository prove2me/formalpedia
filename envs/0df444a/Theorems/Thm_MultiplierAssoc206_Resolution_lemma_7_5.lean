-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_lemma_7_5
-- name    : MultiplierAssoc206.Resolution.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:23:33.66924+00:00
-- url     : https://prove2.me/theorems/ca95f52d-a4ae-4147-94c8-bae8e9c25bc2
-- title:
--   $\rho$ is a $g$-sparse restriction
-- statement:
--   Standing assumptions (§§5–8): $(\mathrm{Mul}_n)_n$ is a strip-local family; $H=(U,V,E)$ has $|U|=m+1$, $|V|=m$ and no isolated vertices; $i,j,k$ are index maps for $H$ with the properties of Lemma 7.3, strip width $g=\lceil\log_2(m+2)\rceil+2$ and bound $n_0$, and $n\ge n_0$; $\rho$ is the restriction of Definition 7.4 on $\mathsf{Assoc}_n$.
--
--   (i) Every partial product of $\mathbf{xy}$ not forced to $0$ by $\rho$ lies in a $g$-column. For each $v\in V$, the partial products not forced to $0$ in the $g$-column $\mathrm{col}_{\mathbf{xy}}(v)$ are exactly
--   $$x_{i(u_e)}\,y_{j(e)}=X_e,\qquad e\in E(v),$$
--   that is, their positions are $\{(i(u_e),j(e)):e\in E(v)\}$, $\rho$ sets each such $x_{i(u_e)}$ to $1$ and leaves $y_{j(e)}$ unset; every other $g$-column contains at most one partial product not forced to $0$. Symmetrically for $\mathbf{yz}$, with the $g$-columns $\mathrm{col}_{\mathbf{yz}}(u)$ holding exactly $y_{j(e)}z_{k(v_e)}=X_e$, $e\in E(u)$.
--
--   (ii) For each of the four multipliers $\mathbf{xy}$, $\mathbf{yz}$, $(\mathbf{xy})\mathbf z$, $\mathbf x(\mathbf{yz})$, the restriction $\rho$ induces a $g$-sparse restriction of its input bit-vectors (for the outer multipliers: the output wires of the inner multiplier and the zero-padded $n$-bit input).
--
--   This lets strip-locality and Observation 4.5 be applied to all four multipliers under $\rho$.
--
--   Differences from the source:
--   - generalization: the maps i, j, k constructed in Lemma 7.3, and a graph of maximum degree at most a constant Δ → any maps with the properties (i)–(iii) of Lemma 7.3, for strip width g = ⌈log₂(m+2)⌉+2 and bound n₀ ≤ n; no degree bound; reason: the paper notes that the rest of the argument uses only the three properties (PDF p.17); the constructed maps have them, and every finite graph has some maximum degree
--   - encoding: the g-column col_xy(v) contains exactly the partial products x_{i(u_e)} y_{j(e)} = X_e, e ∈ E(v) → the positions (i, j) of the partial products not forced to 0 in column col_xy(v) form the set {(i(u_e), j(e)) : e ∈ E(v)}, and at each of them ρ sets x_i to 1 and leaves y_j unset; reason: y_{j(e)} is the edge variable X_e, so x_{i(u_e)} y_{j(e)} = X_e under ρ
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.18 (printed p.17), Lemma 7.5

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Rho

namespace MultiplierAssoc206.Resolution

/-- Lemma 7.5 (ρ is a g-sparse restriction), PDF p.18 (printed p.17). -/
theorem lemma_7_5 (Mul : (n : ℕ) → MulEncoding n) (hMul : StripLocal Mul)
    (m : ℕ) {U V : Type} [Fintype U] [Fintype V] (hU : Fintype.card U = m + 1)
    (hV : Fintype.card V = m) (E : Finset (U × V)) (hE : NoIsolated E)
    {n₀ : ℕ} (M : IndexMaps E (stripWidth m) n₀) (n : ℕ) (hn : n₀ ≤ n) :
    -- (i) for xy
    ((∀ i j : Fin n, ¬ ForcedZero (restrXY Mul n M) i j → stripWidth m ∣ (i : ℕ) + j) ∧
      (∀ v : V, (freeInColumn (restrXY Mul n M) (M.cxy v)).image
          (fun p => ((p.1 : ℕ), (p.2 : ℕ))) =
        (star E (Sum.inr v)).image (fun e => (M.i e.1.1, M.j e))) ∧
      (∀ v : V, ∀ p ∈ freeInColumn (restrXY Mul n M) (M.cxy v),
        (restrXY Mul n M).1 p.1 = some true ∧ (restrXY Mul n M).2 p.2 = none) ∧
      (∀ c : ℕ, stripWidth m ∣ c → (∀ v : V, c ≠ M.cxy v) →
        (freeInColumn (restrXY Mul n M) c).card ≤ 1)) ∧
    -- (i) symmetrically for yz
    ((∀ i j : Fin n, ¬ ForcedZero (restrYZ Mul n M) i j → stripWidth m ∣ (i : ℕ) + j) ∧
      (∀ u : U, (freeInColumn (restrYZ Mul n M) (M.cyz u)).image
          (fun p => ((p.1 : ℕ), (p.2 : ℕ))) =
        (star E (Sum.inl u)).image (fun e => (M.j e, M.k e.1.2))) ∧
      (∀ u : U, ∀ p ∈ freeInColumn (restrYZ Mul n M) (M.cyz u),
        (restrYZ Mul n M).1 p.1 = none ∧ (restrYZ Mul n M).2 p.2 = some true) ∧
      (∀ c : ℕ, stripWidth m ∣ c → (∀ u : U, c ≠ M.cyz u) →
        (freeInColumn (restrYZ Mul n M) c).card ≤ 1)) ∧
    -- (ii)
    (IsGSparse (stripWidth m) (restrXY Mul n M) ∧ IsGSparse (stripWidth m) (restrYZ Mul n M) ∧
      IsGSparse (stripWidth m) (restrXYZ Mul n M) ∧
      IsGSparse (stripWidth m) (restrXYZ' Mul n M)) := by sorry

end MultiplierAssoc206.Resolution
