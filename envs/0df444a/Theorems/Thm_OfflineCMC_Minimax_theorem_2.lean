-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_theorem_2
-- name    : OfflineCMC.Minimax.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:22.683225+00:00
-- url     : https://prove2.me/theorems/7ea13f88-d2bc-48ca-b853-0d3771645788
-- title:
--   Theorem 2 (corrected: the threshold needs dT/ε² and (T/ε²)log(dkT/(ε²δ)); minimax clause read as G.3 Part 1) — sample complexity of the empirical estimator under geometric mixing, and its optimality
-- statement:
--   **(a) Sample complexity.** There are a universal constant $c>1$ and a function $C\mapsto\mathbb C_{pel}(C)$, positive on $(1,\infty)$, with the following property. Let $\{(X_i,a_i)\}$ be any controlled Markov chain with $d\ge1$ states, $k\ge1$ controls and arbitrary adapted controls. Suppose it satisfies, on the window up to $m$:
--
--   1. Assumption 1 with constants $\zeta_1,\zeta_2$;
--   2. Assumption 2 with the integer $T$;
--   3. Assumption 4 with the constant $\mathbb C_\Delta$.
--
--   Let $\varepsilon>0$ and $\delta\in(0,1)$. Let $\rho_\star$, $\zeta^{(\max)}=\max\{\zeta_1,1-\zeta_2\}$, $\mathbb C_{T,\delta}$ and $\mathbb C_{\zeta,\delta}$ be the quantities of p. 14 built with $\mathbb C_{pel}=\mathbb C_{pel}(\mathbb C_\Delta)$. If
--   $$
--   m>c\max\Big\{\frac{4d}{\varepsilon^2(1+\zeta^{(\max)})},\ \frac{dT}{\varepsilon^2},\ \frac T{\varepsilon^2}\log\frac{dkT}{\varepsilon^2\delta},\ \mathbb C_{T,\delta}(\log\mathbb C_{T,\delta})^2,\ \mathbb C_{\zeta,\delta}(\log\mathbb C_{\zeta,\delta})^2\Big\},
--   $$
--   then the empirical estimator of eq. (1.2) satisfies
--   $$
--   \mathbb P\Big(\sup_{l}\big\|\hat M^{(l)}-M^{(l)}\big\|_\infty>\varepsilon\Big)<\delta .
--   $$
--
--   **(b) Minimaxity.** There are universal constants $c_2>0$ and $d_0$ with the following property. Let $d\ge d_0$, $0<p_\star<1/(d+1)$, $0<\varepsilon<1/32$ and $0<\delta<1/2$. For $\sigma\in\{-1,1\}^{\lfloor d/2\rfloor}$, let $M_\sigma$ be the transition matrix (G.19) on $d+1$ states (for odd $d$ the last coordinate before the special state is not perturbed). The hard family of controlled Markov chains (one control, kernel $M_\sigma$, $X_0\sim b$) has three properties:
--
--   1. for every $\sigma$ such a chain exists;
--   2. every such chain satisfies Assumption 1 with $\zeta_1=\zeta_2=p_\star$, Assumption 2 with $T=\lceil3/p_\star\rceil$, and Assumption 4 with $\mathbb C_\Delta=4/3$, for every $m$;
--   3. if $m\le c_2(1-2\delta)\,d/(p_\star\varepsilon^2)$, then for every estimator $\tilde M$, i.e. every function of the observed states $X_0,\dots,X_{m+1}$, there is a $\sigma$ such that every chain of the family with kernel $M_\sigma$ has
--   $$
--   \mathbb P\big(\|\tilde M-M_\sigma\|_\infty>\varepsilon\big)>\delta .
--   $$
--
--   On this family $T\asymp1/p_\star$, so (b) shows that the leading term $dT/\varepsilon^2$ of (a) cannot be improved beyond a universal constant.
--
--   Theorem 2 is the main result of the paper. The empirical estimator recovers all $k$ transition matrices of a controlled Markov chain driven by arbitrary, possibly non-Markovian logging controls. When the chain mixes geometrically, the number of samples it needs is minimax optimal up to universal constants and logarithmic factors.
--
--   **Formalization Note**
--   1. $\|\cdot\|_\infty$ is the maximum row $\ell^1$ sum, and the estimator uses Lean's $0/0=0$.
--   2. $c$ and the function $\mathbb C_{pel}$ are chosen before $d$, $k$, the chain and $m$.
--   3. The chains of (b) live on an arbitrary probability space; their existence (b1) is asserted on the path space $(\mathrm{Fin}(d+1))^{\mathbb N}$.
--   4. The states of (b) are `Fin (d + 1)` with the special state last, and sign vectors are maps into $\mathbb Z^\times$.
--
--   Differences from the source:
--   - correction: $m>c\max\{\frac{4d}{\varepsilon^2(1+\max\{\zeta_1,1-\zeta_2\})},\mathbb C_{T,\delta}(\log\mathbb C_{T,\delta})^2,\mathbb C_{\zeta,\delta}(\log\mathbb C_{\zeta,\delta})^2\}$ → the same maximum with the two further terms $dT/\varepsilon^2$ and $(T/\varepsilon^2)\log(dkT/(\varepsilon^2\delta))$; reason: as printed (a) is false. Take one control, $X_i$ i.i.d. uniform on $d$ even states ($M$ all entries $1/d$), $S_i$ the first $d/2$ states ($\zeta_1=\zeta_2=1/2$), $T=d+1$, $\bar\eta\equiv0$ ($\mathbb C_\Delta=2$), $\rho_\star=1/d$, $\varepsilon=1$, $\delta=1/2$. Then $\mathbb C_\zeta=O(1)$ and $\mathbb C_T=O(d)$, so the printed threshold is $O(d(\log d)^3)$ for every $c$ and every $\mathbb C_{pel}(2)>0$. At such $m$ each state is visited $O((\log d)^3)$ times, the row error is at least $2(1-N_s/d)\to2>\varepsilon$, and the probability tends to $1>\delta$. The term $dT/\varepsilon^2$ is what Proposition 1 (corrected) needs at $n_{low}=m/(4T)$; the term $(T/\varepsilon^2)\log(dkT/(\varepsilon^2\delta))$ is Theorem 1's term, needed for the $\log(1/\delta)$ dependence at fixed $d$.
--   - reading: "is minimax upto log and loglog terms whenever $0<\varepsilon<1/32$" → clause (b), the content of App. G.3 Part 1, with universal constants $c_2$, $d_0$; reason: the printed phrase is not a precise statement, and its quantified content in the paper is G.3. Part 2 is not used: its Case I is false (in the class $H_\iota$ of (E.2) two members differ by $\varepsilon$, not $2\varepsilon$, in each differing row, so the midpoint matrix has error $\le\varepsilon/2$), and Case II gives no argument. The page's constant $\log2/32768$ rests on (G.21), which is not Tsybakov's Theorem 2.5 as printed. $T=\lceil3/p_\star\rceil$ replaces the page's bound $T\le d/p_\star$: the return time to the special state is geometric with mean $1/p_\star$, and to any other state it has mean below $2.1d<3/p_\star$.
--   - reading: "for all $\varepsilon,\delta>0$" → $\varepsilon>0$ and $\delta\in(0,1)$; reason: "the setting of Theorem 1" has $\delta\in(0,1)$, and $\log(6dk/\delta)$ in $\mathbb C_{T,\delta}$ presupposes it
--   - reading: "$\mathbb C_{pel}$ as in Proposition 3", "depending only upon $\mathbb C_\Delta$" → a function $\mathbb C_{pel}(\cdot)$, positive on $(1,\infty)$, quantified with $c$ before the chain; reason: this is the meaning of "depending only upon $\mathbb C_\Delta$"
--   - reading: first hitting time with "$(X_j\ne s,a_j\ne l)$" → first time $n\ge1$ with $(X_n,a_n)=(s,l)$; reason: as in the recursive clause of Definition 2
--   - reading: sample $(X_0,a_0),\dots,(X_m,a_m)$ → counts of eq. (1.1) over $i=1,\dots,m$, reading $X_{m+1}$; reason: eq. (1.1) defines $N^{(l)}_{s,t}$ with $X_{i+1}$ for $i\le m$
--   - reading: Assumption 4 for $i<j$ → for $0\le i<j\le m$ (empty history at $i=0$); reason: eq. (2.1) defines $\bar\eta_{i,j}$ for $i<j\le m$ with $\hbar^{i-1}_0\in(\chi\times\mathbb I)^i$
--   - generalization: Assumption 1 "for all times $i$" → at the times $1\le i\le m$; reason: weaker hypothesis implied by the paper's
--   - generalization: Assumption 4 with "$\mathbb C_\Delta>1$ independent of $m$" → in (a), the bound on $\bar\eta_{i,j}$ (window up to $m$) at the given sample size $m$ only; reason: a weaker hypothesis implied by the paper's; $c$ and $\mathbb C_{pel}$ still depend on nothing but $\mathbb C_\Delta$, so (a) specializes to the source's
--   - generalization: estimators $\hat{\mathbb M}:(\chi\times\mathbb I)^m\to\mathcal M_\chi$ → every function of $X_0,\dots,X_{m+1}$; reason: a lower bound against estimators with more data implies the page's; $X_{m+1}$ is the state the empirical estimator reads
--   - reading: "$d>2$" → $d\ge d_0$ for a universal $d_0$; reason: the page's derivation of the constant goes through (G.21), which is not valid as printed, and Fano's inequality gives (b3) only for $d$ large; with a single sign coordinate (two hypotheses) the clause fails for $\delta$ close to $1/2$, since an estimator then has worst-case error probability $(1-\mathrm{TV})/2<1/2$; a rate statement with universal constants is unaffected
--   - reading: G.3 Part 1's conclusion "whenever $m\le\frac{d(1-2\delta)\log2}{32768p_\star\varepsilon^2}$, … $>\delta$", with no range for $\delta$ → $0<\delta<1/2$ in (b); reason: the factor $1-2\delta$ admits no sample size for $\delta>1/2$, and the page's lower bound $\frac12(1-\cdots)$ never exceeds $1/2$, so the page's argument covers exactly $\delta<1/2$
--   - reading: the page fixes no initial law for the chains $M_\sigma$ → $X_0\sim b$; reason: any law not depending on $\sigma$ serves the argument, and $b$ is the law the page's path divergences (G.22) use
--   - generalization: "$d+1$ states where $d$ is even; the odd case is handled similarly" → every $d\ge d_0$, with $\sigma\in\{-1,1\}^{\lfloor d/2\rfloor}$ and the leftover coordinate of $\eta(\sigma)$ unperturbed when $d$ is odd; reason: Theorem 2 claims minimaxity for every number of states; on even $d$ the Lean family is exactly (G.19)
--   - encoding: $\hat M^{(l)}_{s,t}=N^{(l)}_{s,t}/N^{(l)}_s$ → Lean division with $0/0=0$; reason: every sample with $N^{(l)}_s=0$ lies in $\{N^{(l)}_s<n_{low}\}$, whose probability the proof bounds under any convention
--   - encoding: Assumption 2's supremum of conditional expectations → a.s. finite integrable return times and an $\omega$-dependent witness $T'<T$; reason: equivalent to the paper's bound
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 14, Theorem 2 (constants on p. 14; setting of Theorem 1, pp. 12–13); proof App. G.2–G.3, pp. 48–53

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC
import Definitions.Def_OfflineCMC_Minimax_Model
import Definitions.Def_OfflineCMC_Minimax_HardFamily

universe u

namespace OfflineCMC.Minimax

open MeasureTheory

theorem theorem_2 :
    (∃ c : ℝ, 1 < c ∧ ∃ Cpel : ℝ → ℝ, (∀ x : ℝ, 1 < x → 0 < Cpel x) ∧
      ∀ (d k : ℕ), 0 < d → 0 < k →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (C : CMC d k μ) (m : ℕ) (ζ₁ ζ₂ : ℝ) (T : ℕ) (CΔ ε δ : ℝ),
        C.Assumption1 m ζ₁ ζ₂ → C.Assumption2 T → C.Assumption4 m CΔ →
        0 < ε → 0 < δ → δ < 1 →
        c * max (max (max (max
            (4 * (d : ℝ) / (ε ^ 2 * (1 + zetaMax ζ₁ ζ₂)))
            ((d : ℝ) * (T : ℝ) / ε ^ 2))
            ((T : ℝ) / ε ^ 2 * Real.log ((d : ℝ) * (k : ℝ) * (T : ℝ) / (ε ^ 2 * δ))))
            (CT (Cpel CΔ) CΔ (C.rhoStar m) T * logFactor d k δ *
              Real.log (CT (Cpel CΔ) CΔ (C.rhoStar m) T * logFactor d k δ) ^ 2))
            (Czeta (Cpel CΔ) CΔ (C.rhoStar m) (zetaMax ζ₁ ζ₂) * logFactor d k δ *
              Real.log (Czeta (Cpel CΔ) CΔ (C.rhoStar m) (zetaMax ζ₁ ζ₂) * logFactor d k δ) ^ 2)
          < (m : ℝ) →
        μ.real {ω | ε < C.estError m ω} < δ) ∧
    (∃ c₂ : ℝ, 0 < c₂ ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ p ε δ : ℝ, 0 < p → p < 1 / ((d : ℝ) + 1) → 0 < ε → ε < 1 / 32 → 0 < δ → δ < 1 / 2 →
        (∀ σ : Fin (d / 2) → ℤˣ, ∃ μ : Measure (ℕ → Fin (d + 1)), IsProbabilityMeasure μ ∧
          ∃ C : CMC (d + 1) 1 μ, IsHardRealization d p ε σ C) ∧
        (∀ (σ : Fin (d / 2) → ℤˣ) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (C : CMC (d + 1) 1 μ), IsHardRealization d p ε σ C →
          ∀ m : ℕ, C.Assumption1 m p p ∧ C.Assumption2 ⌈3 / p⌉₊ ∧ C.Assumption4 m (4 / 3)) ∧
        ∀ m : ℕ, (m : ℝ) ≤ c₂ * (1 - 2 * δ) * (d : ℝ) / (p * ε ^ 2) →
          ∀ f : (Fin (m + 2) → Fin (d + 1)) → Fin (d + 1) → Fin (d + 1) → ℝ,
          ∃ σ : Fin (d / 2) → ℤˣ,
            ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
              (C : CMC (d + 1) 1 μ), IsHardRealization d p ε σ C →
              δ < μ.real {ω | ε < infNorm (fun s t =>
                f (fun i => C.X i ω) s t - hardMatrix d p ε σ s t)}) := by sorry

end OfflineCMC.Minimax
