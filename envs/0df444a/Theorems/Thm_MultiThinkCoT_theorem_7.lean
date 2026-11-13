-- Prove2me | Theorems.Thm_MultiThinkCoT_theorem_7
-- name    : MultiThinkCoT.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:59.635307+00:00
-- url     : https://prove2.me/theorems/18b30a70-75bc-4e1b-8f4b-d30e4716dbc7
-- title:
--   Theorem 7 — boosting adaptive CoT sources reaches error $\varepsilon$ with $O(\mathrm{VCdim})$ CoTs per source
-- statement:
--   There is a universal constant $c>0$ and there are budget functions $\mathrm{Mst},\mathrm{Mst}'$ with $\mathrm{Mst}(v)\le cv$, $\mathrm{Mst}'(w)\le cw$, fixed before everything else, such that the following four statements hold.
--
--   1. **Learning guarantee.** Let $\mathcal F$ be any base class, $T$ any generation length and $\mathcal X$ any domain with $v=\mathrm{VCdim}(\mathcal F^{\mathrm{e2e}\text{-}T})<\infty$. Let $\mathcal D$ be any distribution over $\mathcal X$, $h^\star\in\mathcal F^{\mathrm{e2e}\text{-}T}$ any target, and $\varepsilon,\delta\in(0,1)$. Take any $m\ge1$ with
--   $$
--   m\ \ge\ m(\varepsilon,\delta)=c\,\frac{v\log(2/\varepsilon)\log^2(2v/\varepsilon)+\log\delta^{-1}}{\varepsilon}.
--   $$
--   Run Algorithm 1 with $K=\lceil8\log(2m)\rceil$ and $M_\star=\mathrm{Mst}(v)$, collecting CoTs under Definition 2.3 with any Consistent oracle and against any adaptive adversary. With probability at least $1-\delta$ over the draw of $S_{\mathrm{e2e}}$ and the algorithm's internal randomness, it returns $\hat h_K$ with $L_{\mathcal D,h^\star}(\hat h_K)\le\varepsilon$. On every run, the number of generators used satisfies
--   $$
--   \kappa\ \le\ K\,\lceil\log_2(2K/\delta)\rceil,
--   $$
--   and each requested subset has at most $M_\star$ indices.
--   2. **Runtime.** Let $(\mathcal F_d)_d$ be a hierarchy over domains $\mathcal X_d\subseteq\{0,1\}^{\le d}$ with a tractable Consistent oracle, polynomial-time next-token evaluation and $\mathrm{VCdim}(\mathcal F_d^{\mathrm{e2e}\text{-}T})\le\mathrm{poly}(d,T)$. Choosing $m=\lceil m(\varepsilon,\delta)\rceil$, every run plus the evaluation of its output on an input of $\mathcal X_d$ costs at most $\mathrm{poly}(d,T,\varepsilon^{-1},\log\delta^{-1})$.
--   3. **Relaxed protocol.** If the adversary chooses $f_k$ before observing $S_k$, the guarantee of (1) holds with $M_\star=\mathrm{Mst}'(w)$, where $w=\mathrm{VCdim}(\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F))<\infty$.
--   4. **Relaxed budget.** $\mathrm{Mst}'(w)=O(\min\{\log|\mathcal F|,\mathrm{VCdim}(\mathcal F)\log T\})$, where $\mathrm{VCdim}(\mathcal F)$ is taken over $\mathcal X\times\{0,1\}^{\le T-1}$.
--
--   The per-source budget does not depend on $\varepsilon$: small homogeneous batches of CoTs from adaptively chosen, heterogeneous sources suffice for arbitrarily small end-to-end error, using only a consistency oracle for single-source data.
--
--   **Formalization Note**
--   - **Probability.** $\mathcal D$ is a probability mass function. The probability is over the i.i.d. sample followed by the run distribution of Algorithm 1. The oracle and the adversary strategy are fixed before the sample.
--   - **Adversary.** A strict adversary sees the inputs, the history and the current subset; a relaxed one sees only the inputs and the history.
--   - **Logarithms.** $\log$ is natural and $\log_2$ is base $2$.
--   - **Runtime.**
--     - The cost is accumulated inside the definition of Algorithm 1.
--     - Polynomial bounds are of the form $A(d+n+N+1)^a$ for the oracle on $N$ pairs of maximal length $n$, $B(d+\ell+1)^b$ for a next-token evaluation, and $V(d+T+1)^w$ for the VC dimension.
--     - The conclusion is a bound $C(d+T+\lceil1/\varepsilon\rceil+\lceil\log\delta^{-1}\rceil+2)^k$, with $C,k$ depending only on these bounds.
--     - In this clause $m=\max\{1,\lceil m(\varepsilon,\delta)\rceil\}$.
--   - **Relaxed budget.** $\mathrm{Mst}'(w)\le c\log|\mathcal F|$ for finite $\mathcal F$, and $\mathrm{Mst}'(w)\le c\,p\max\{1,\log T\}$ when $\mathrm{VCdim}(\mathcal F)$ over the prefix domain is $p$.
--
--   Differences from the source:
--   - generalization: M⋆ = O(VCdim(F^{e2e-T})), chosen in the proof via Lemma F.2 for the drawn training set → M⋆ = Mst(v) for a function Mst with Mst v ≤ c v fixed together with c before F, T, X, D, h⋆, ε, δ, m and the sample (likewise Mst' in the relaxed protocol); reason: a uniform choice is in particular a valid choice in every instance; it makes 'independent of ε' (p.9) explicit
--   - encoding: any size m ≥ m(ε, δ) → 1 ≤ m and c(v log(2/ε) log²(2v/ε) + log δ⁻¹)/ε ≤ m; reason: line 1 of Algorithm 1 divides by m; m = 0 is only admitted when v = 0 and δ is close to 1
--   - encoding: log(2/ε) log²(2VCdim/ε) in m(ε, δ) (log u read as max{1, log u}, p.16) → plain natural logarithms log(2/ε), log(2v/ε)²; reason: 2/ε > 2 and, when v ≥ 1, 2v/ε > 2, so the two readings differ by a factor at most 1/log 2, absorbed in c; when v = 0 the term vanishes in both
--   - encoding: VCdim(F^{e2e-T}) (finiteness implicit) → vcDim (e2eClass F T X) = v with v : ℕ (and w : ℕ for VCdim(L^{CoT-T}(F)) in the relaxed clause); reason: an infinite VC dimension makes m(ε, δ), resp. the budget, infinite and the clause vacuous
--   - encoding: a distribution D ∈ ∆(X) on X ⊆ {0,1}* → D : PMF X; reason: X is countable, so every distribution on it is a probability mass function
--   - encoding: the adversary chooses f_k from the history and S_k (Definition 2.3); the learner uses a Consistent oracle → ∀ deterministic strategies (seeing the inputs, the history and, strictly, the current subset) and ∀ oracle functions meeting IsConsistentOracle F, both fixed before the sample; reason: a randomized adversary is a mixture of deterministic ones; the oracle of Definition 1.1 is any algorithm with that output property
--   - reading: f_k^{e2e-T} ≡ h⋆ → f_k^{e2e-T}(x) = h⋆(x) for every x ∈ X, for every choice the strategy can make; reason: ≡ is identity of functions on the domain (Definition 2.3)
--   - generalization: generation length T (positive in the paper's examples) → every T : ℕ, including T = 0; reason: at T = 0 every end-to-end map is the same function, VCdim = 0, and the clause reduces to its T ≥ 1 form trivially; the statement contains every T ≥ 1
--   - reading: the overall runtime is poly(d, T, ε⁻¹, log δ⁻¹) (no machine model named) → the cost accumulated line by line in alg1 (unit-cost real arithmetic, oracle and next-token charges oc, ec) of every run plus one evaluation of the output on x ∈ X_d is ≤ C(d + T + ⌈1/ε⌉ + ⌈log δ⁻¹⌉ + 2)^k, with C, k depending only on the polynomial bounds A, a, B, b, V, w; reason: a polynomial with nonnegative coefficients is bounded by C(1 + Σ args)^k; the paper's §6.1 counts both producing and evaluating ĥ
--   - encoding: choosing m = ⌈m(ε, δ)⌉ → m = max{1, ⌈m(ε, δ)⌉}; reason: m ≥ 1 as above
--   - reading: M⋆ = O(VCdim(L^{CoT-T}(F))) = O(min{log |F|, VCdim(F) log T}) → Mst' w ≤ c w; Mst' w ≤ c log |F| for finite F; Mst' w ≤ c p max{1, log T} when VCdim(F) over X × {0,1}^{≤T−1} is p; reason: log |F| = ∞ for infinite F; max{1, log T} per p.16 (the bound must hold at T = 1)
--   - encoding: Algorithm 1's input ε → omitted; reason: no line of Algorithm 1 uses ε
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §7.3, Theorem 7, pp.23–25 (PDF pp.23–25)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MultiThinkCoT_e2eClass
import Definitions.Def_MultiThinkCoT_cotLossClass
import Definitions.Def_MultiThinkCoT_prefixClass
import Definitions.Def_MultiThinkCoT_endToEndError
import Definitions.Def_MultiThinkCoT_alg1

namespace MultiThinkCoT

/-- **Theorem 7 (More technical version of Theorem 3)**, pp.23–25 (PDF pp.23–25).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

There is a universal constant `c > 0` such that the following holds, with per-source budgets
`M⋆ = Mst(VCdim(F^{e2e-T})) ≤ c VCdim(F^{e2e-T})` and, in the relaxed protocol,
`M⋆ = Mst'(VCdim(L^{CoT-T}(F))) ≤ c VCdim(L^{CoT-T}(F))`.

1. For any base class `F`, generation length `T`, domain `X` with `VCdim(F^{e2e-T}) = v < ∞`,
   distribution `D` over `X`, target `h⋆ ∈ F^{e2e-T}`, `ε, δ ∈ (0,1)`, and any training-set size
   `m ≥ m(ε, δ) = c (v log(2/ε) log²(2v/ε) + log δ⁻¹)/ε` (`m ≥ 1`), Algorithm 1 with
   `K = ⌈8 log(2m)⌉` and `M⋆ = Mst(v)`, collecting CoTs under Definition 2.3 against any adaptive
   adversary and with any Consistent oracle, returns with probability at least `1 − δ` over the
   draw of `S_e2e` and its internal randomness a predictor `ĥ_K` with `L_{D,h⋆}(ĥ_K) ≤ ε`; on every
   run the number of generators used is `κ ≤ K ⌈log₂(2K/δ)⌉`, and every requested subset has at
   most `M⋆` indices.
2. (Runtime.) For a hierarchy `(F_d)_d` over `X_d ⊆ {0,1}^{≤d}` with a tractable Consistent oracle
   and `VCdim(F_d^{e2e-T}) ≤ poly(d, T)`, choosing `m = ⌈m(ε, δ)⌉`, the overall runtime (every run,
   plus evaluating the output on an input of `X_d`) is at most `poly(d, T, ε⁻¹, log δ⁻¹)`.
3. (Relaxed protocol.) If the adversary chooses `f_k` before observing `S_k`, the same guarantee
   holds with `M⋆ = Mst'(VCdim(L^{CoT-T}(F)))`, and
   `Mst'(VCdim(L^{CoT-T}(F))) = O(min{log |F|, VCdim(F) log T})`, `VCdim(F)` over
   `X × {0,1}^{≤T−1}`.

**Formalization Note.**
* `Mst`, `Mst'` are functions of the VC dimension alone, fixed together with `c` before every other
  object (`F`, `T`, `X`, `D`, `h⋆`, `ε`, `δ`, `m`, the sample): "independent of ε".
* `D` is a `PMF` on the countable domain; the probability is over `iidSample D m` bound with the
  run distribution `alg1`. The oracle (any `O` with `IsConsistentOracle F O`) and the adversary
  (any strict, resp. relaxed, strategy for `h⋆`, which sees the inputs and the history, and in the
  strict protocol the current subset) are fixed before the sample is drawn.
* `log` is the natural logarithm, `log₂` is `Real.logb 2`, `⌈·⌉` is `Nat.ceil`. The factors
  `log(2/ε)` and `log²(2v/ε)` are plain logarithms (their arguments exceed `2` whenever `v ≥ 1`,
  so `max{1, log}` changes them only by a constant factor).
* `m ≥ 1` is required (line 1 of Algorithm 1 divides by `m`). In the runtime clause
  `m = max 1 ⌈m(ε, δ)⌉`.
* Runtime: the cost accumulated inside `alg1` line by line (unit-cost real arithmetic). A
  polynomial is a bound `C (d + T + ⌈1/ε⌉ + ⌈log δ⁻¹⌉ + 2)^k`, with `C, k` depending only on the
  polynomial bounds `A (d + n + N + 1)^a` on the oracle cost, `B (d + ℓ + 1)^b` on the next-token
  cost (§6.1, p.17) and `V (d + T + 1)^w` on the VC dimension.
* The relaxed budget bound: `Mst'(w) ≤ c log |F|` for finite `F` and `Mst'(w) ≤ c p max{1, log T}`
  when `VCdim(F)` over `X × {0,1}^{≤T−1}` is `p`, whenever `VCdim(L^{CoT-T}(F)) = w`.
-/
theorem theorem_7 :
    ∃ c : ℝ, 0 < c ∧ ∃ Mst Mst' : ℕ → ℕ,
      (∀ v, (Mst v : ℝ) ≤ c * v) ∧ (∀ w, (Mst' w : ℝ) ≤ c * w) ∧
      -- (i) the learning guarantee, the number of generators and the per-round budget
      (∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (v : ℕ),
        UnderstandingML.vcDim (e2eClass F T X) = v →
        ∀ (D : PMF X) (hstar : X → Bool), hstar ∈ e2eClass F T X →
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∀ m : ℕ, 1 ≤ m →
          c * ((v : ℝ) * Real.log (2 / ε) * Real.log (2 * v / ε) ^ 2 + Real.log (1 / δ)) / ε ≤ m →
        ∀ (O : List (List Bool × Bool) → Gen) (oc : ℕ → ℕ → ℕ) (ec : ℕ → ℕ),
          IsConsistentOracle F O →
        ∀ A : (Fin m → X) → History m → Finset (Fin m) → Gen, IsStrictAdversary F T X hstar A →
          ((iidSample D m).bind fun xs =>
              alg1 T O oc ec ⌈8 * Real.log (2 * m)⌉₊ (Mst v) δ (fun i => (xs i).1)
                (fun i => hstar (xs i)) (A xs)).toOuterMeasure
              {r | ε < endToEndError D hstar (fun x => r.pred.eval T x.1)} ≤ ENNReal.ofReal δ ∧
          ∀ r ∈ ((iidSample D m).bind fun xs =>
              alg1 T O oc ec ⌈8 * Real.log (2 * m)⌉₊ (Mst v) δ (fun i => (xs i).1)
                (fun i => hstar (xs i)) (A xs)).support,
            r.kappa ≤ ⌈8 * Real.log (2 * m)⌉₊ *
                ⌈Real.logb 2 (2 * (⌈8 * Real.log (2 * m)⌉₊ : ℝ) / δ)⌉₊ ∧
              r.maxS ≤ Mst v) ∧
      -- (ii) polynomial runtime for a hierarchy with a tractable Consistent oracle
      (∀ A a B b V w : ℕ, ∃ C k : ℕ,
        ∀ (Fh : ℕ → Set Gen) (Xh : ℕ → Set (List Bool)),
          (∀ d, ∀ x ∈ Xh d, x.length ≤ d) →
          (∀ d T, ∃ v : ℕ, UnderstandingML.vcDim (e2eClass (Fh d) T (Xh d)) = v ∧
            v ≤ V * (d + T + 1) ^ w) →
        ∀ (oc : ℕ → ℕ → ℕ → ℕ) (ec : ℕ → ℕ → ℕ),
          (∀ d n N, oc d n N ≤ A * (d + n + N + 1) ^ a) → (∀ d l, ec d l ≤ B * (d + l + 1) ^ b) →
        ∀ (d T : ℕ) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∀ (O : List (List Bool × Bool) → Gen), IsConsistentOracle (Fh d) O →
        ∀ hstar ∈ e2eClass (Fh d) T (Xh d),
        ∀ m : ℕ, m = max 1 ⌈c * (((UnderstandingML.vcDim (e2eClass (Fh d) T (Xh d))).toNat : ℝ) *
            Real.log (2 / ε) *
            Real.log (2 * ((UnderstandingML.vcDim (e2eClass (Fh d) T (Xh d))).toNat : ℝ) / ε) ^ 2
            + Real.log (1 / δ)) / ε⌉₊ →
        ∀ Adv : (Fin m → Xh d) → History m → Finset (Fin m) → Gen,
          IsStrictAdversary (Fh d) T (Xh d) hstar Adv →
        ∀ xs : Fin m → Xh d,
        ∀ r ∈ (alg1 T O (oc d) (ec d) ⌈8 * Real.log (2 * m)⌉₊
            (Mst (UnderstandingML.vcDim (e2eClass (Fh d) T (Xh d))).toNat) δ
            (fun i => (xs i).1) (fun i => hstar (xs i)) (Adv xs)).support,
        ∀ x ∈ Xh d,
          r.cost + r.pred.evalCost (ec d) T x ≤
            C * (d + T + ⌈1 / ε⌉₊ + ⌈Real.log (1 / δ)⌉₊ + 2) ^ k) ∧
      -- (iii) the relaxed protocol
      (∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (v w : ℕ),
        UnderstandingML.vcDim (e2eClass F T X) = v →
        UnderstandingML.vcDim (cotLossClass F T X) = w →
        ∀ (D : PMF X) (hstar : X → Bool), hstar ∈ e2eClass F T X →
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∀ m : ℕ, 1 ≤ m →
          c * ((v : ℝ) * Real.log (2 / ε) * Real.log (2 * v / ε) ^ 2 + Real.log (1 / δ)) / ε ≤ m →
        ∀ (O : List (List Bool × Bool) → Gen) (oc : ℕ → ℕ → ℕ) (ec : ℕ → ℕ),
          IsConsistentOracle F O →
        ∀ R : (Fin m → X) → History m → Gen, IsRelaxedAdversary F T X hstar R →
          ((iidSample D m).bind fun xs =>
              alg1 T O oc ec ⌈8 * Real.log (2 * m)⌉₊ (Mst' w) δ (fun i => (xs i).1)
                (fun i => hstar (xs i)) (fun hist _ => R xs hist)).toOuterMeasure
              {r | ε < endToEndError D hstar (fun x => r.pred.eval T x.1)} ≤ ENNReal.ofReal δ ∧
          ∀ r ∈ ((iidSample D m).bind fun xs =>
              alg1 T O oc ec ⌈8 * Real.log (2 * m)⌉₊ (Mst' w) δ (fun i => (xs i).1)
                (fun i => hstar (xs i)) (fun hist _ => R xs hist)).support,
            r.kappa ≤ ⌈8 * Real.log (2 * m)⌉₊ *
                ⌈Real.logb 2 (2 * (⌈8 * Real.log (2 * m)⌉₊ : ℝ) / δ)⌉₊ ∧
              r.maxS ≤ Mst' w) ∧
      (∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (w : ℕ),
        UnderstandingML.vcDim (cotLossClass F T X) = w →
        (F.Finite → (Mst' w : ℝ) ≤ c * Real.log F.ncard) ∧
        (∀ p : ℕ, UnderstandingML.vcDim (prefixClass F T X) = p →
          (Mst' w : ℝ) ≤ c * p * max 1 (Real.log T))) := by sorry

end MultiThinkCoT
