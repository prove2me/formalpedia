-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_lemma_3
-- name    : LinMatroidSecretary.Online.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:37.448936+00:00
-- url     : https://prove2.me/theorems/ef7d0dac-6040-4664-8b0e-6956e5bf553a
-- title:
--   Lemma 3 — Algorithm 1 is well defined and satisfies (i)–(v)
-- statement:
--   Run Algorithm 1 with sample size $1\le k<n$ on a ground set $R$ of $n$ elements with any value order and any vectors $v:R\to F^d$ over a finite field $F$; the arrival order is uniform and the decisions follow the algorithm. Then:
--
--   1. **(well-defined)** the acceptance probabilities lie in $[0,1]$, and for every $X\subseteq R$ with $|X|>k$ the chosen $p_X$ is a feasible solution of $\mathrm{LP}(X)$ built from the distributions $\mu_{X-e}$ of the table;
--   2. **(ii)** every selected set occurring with positive probability is independent;
--
--   and for every fixed set $X\subseteq R$:
--
--   3. **(i)** for every subspace $U$, $\Pr[\text{the first }|X|\text{ arrivals form }X\text{ and }\langle\mathrm{ALG}\rangle=U\text{ after them}]=\Pr[\text{the first }|X|\text{ arrivals form }X]\cdot\mu_X(U)$;
--   4. **(iii)** if $|X|\ge k$, then $\mu_X$ satisfies the Dimension Invariant Inequality (1);
--   5. **(iv)** if $|X|=i>k$ and $e\in\mathrm{OPT}(X)$, then with $e$ the $i$-th arrival,
--   $$\Pr[e\text{ accepted},\ \text{first }i\text{ arrivals}=X,\ e\text{ arrives }i\text{-th}]=\frac{k}{i-1}\,\Pr[\text{first }i\text{ arrivals}=X,\ e\text{ arrives }i\text{-th}];$$
--   6. **(v)** all entries $\mu_X(U)$ and $p_X(e,W)$ ($e\in X$, $W\in\operatorname{supp}\mu_{X-e}$) are rational.
--
--   Property (iv), averaged over the arrival position, is what yields the $1/e$ bound of Theorem 1.
--
--   Differences from the source:
--   - encoding: conditional statements (i), (iv) given X is the set of the first arrivals (and e arrives last) → joint-probability identities P[A ∧ B] = P[B] · c; reason: equivalent whenever P[B] > 0, and avoids conditioning on null events
--   - encoding: the algorithm is well-defined up to the processing of X → its acceptance probabilities lie in [0,1], and for |X| > k the chosen p_X is feasible for LP(X); reason: well-definedness means the choice rule never falls back on an infeasible LP; for |X| ≤ k the entries are fixed
--   - encoding: (ii) ALG is always independent → every (σ, b) of positive probability yields an independent ALG(σ, b); reason: outcomes of probability zero never occur
--   - encoding: the table (µ_Y, p_Y) depends only on Y and the data revealed for its elements → the table is computed from the vectors of Y sorted by value order, with LP variables indexed by rank; reason: this is the paper's fixed choice rule made label-free; no instance changes
--   - encoding: internal randomness of the algorithm → behavioural randomness: one acceptance probability per step, a function of the observed history; reason: Algorithm 1 accepts with probability p_X(e, ⟨ALG⟩) using fresh randomness at each step
--   - encoding: finite-dimensional vector spaces, subspaces, probability distributions and integer dimensions → vectors in Fin d → F, Submodule lattices, Finsupp distributions and real casts of finrank (including real subtraction in Δ); reason: every finite-dimensional represented instance has coordinates; over a finite field all subspaces form a finite set, so finite support loses no distributions, and casts preserve the exact dimensions
--   - encoding: acceptance probabilities for genuine online histories up to n arrivals → Policy.Valid requires probabilities for all steps and all input comparison patterns, including unrealizable histories; reason: this is a total completion of the rule; the chosen feasible LP coordinates lie in [0,1] and unused coordinates are zero, so it adds no condition on an instance
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), Lemma 3, PDF pp. 10–11 (printed pp. 8–9), with Algorithms 1–2

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Setting
import Definitions.Def_LinMatroidSecretary_Online_DimensionLP
import Definitions.Def_LinMatroidSecretary_Online_Algorithm

namespace LinMatroidSecretary.Online

/-- Lemma 3 (PDF pp. 10–11, printed 8–9). Algorithm 1 with sample size `1 ≤ k < n`, run on any
finite ground type `R` with `n` elements, value order and vectors `v`:
* (well-defined) its acceptance probabilities are probabilities, and for every `X` with
  `|X| > k` the chosen `p_X` is a feasible solution of `LP(X)` built from the `µ_{X−e}`;
* (i) `P[first |X| arrivals = X ∧ ⟨ALG⟩ = U after them] = P[first |X| arrivals = X] · µ_X(U)`;
* (ii) every selected set occurring with positive probability is independent;
* (iii) if `|X| ≥ k`, `µ_X` satisfies the Dimension Invariant Inequality (1);
* (iv) if `|X| = i > k` and `e ∈ OPT(X)`, then with `t = i − 1` (0-based last position of the
  prefix), `P[e accepted ∧ first i = X ∧ σ t = e] = (k/(i−1)) · P[first i = X ∧ σ t = e]`;
* (v) all entries of `µ_X` and of `p_X` are rational.

`π` names Algorithm 1 (`hπ : π = alg1 k`). -/
theorem lemma_3 (F : Type*) [Field F] [Fintype F] (d n k : ℕ) (hk : 1 ≤ k)
    (hkn : k < n) {R : Type*} [Fintype R] [LinearOrder R] (hR : Fintype.card R = n)
    (v : R → Fin d → F) (π : Policy n d F) (hπ : π = alg1 k) :
    π.Valid ∧
    (∀ (σ : Fin n ≃ R) (b : Fin n → Bool), 0 < runProb π v σ b →
      LinearIndepOn F v (alg σ b : Set R)) ∧
    ∀ X : Finset R,
      (k < X.card →
        LPFeasible v X k (fun e => muSet v k (X.erase e)) (pSet v k X)) ∧
      (∀ U : Submodule F (Fin d → F),
        prob π v (fun σ b => prefixSet σ X.card = X ∧
            Submodule.span F (v '' (prefixAlg σ b X.card : Set R)) = U) =
          prob π v (fun σ b => prefixSet σ X.card = X) * muSet v k X U) ∧
      (k ≤ X.card → DimInvariant (muSet v k X) X.card k) ∧
      (k < X.card → ∀ e ∈ OPT F v X, ∀ t : Fin n, (t : ℕ) + 1 = X.card →
        prob π v (fun σ b => prefixSet σ X.card = X ∧ σ t = e ∧ b t = true) =
          ((k : ℝ) / ((X.card : ℝ) - 1)) *
            prob π v (fun σ b => prefixSet σ X.card = X ∧ σ t = e)) ∧
      ((∀ U : Submodule F (Fin d → F), ∃ q : ℚ, muSet v k X U = (q : ℝ)) ∧
        ∀ e ∈ X, ∀ W ∈ (muSet v k (X.erase e)).support, ∃ q : ℚ, pSet v k X e W = (q : ℝ)) := by sorry

end LinMatroidSecretary.Online
