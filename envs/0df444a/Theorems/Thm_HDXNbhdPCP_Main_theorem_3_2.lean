-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_theorem_3_2
-- name    : HDXNbhdPCP.Main.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:59:51.667256+00:00
-- url     : https://prove2.me/theorems/558b8641-b85f-4689-80f7-12832131f672
-- title:
--   Theorem 3.2 — the local-to-global theorem for the neighbourhood test
-- statement:
--   There is a universal constant $C>0$ (and a universal exponent $e>0$) such that for every $\beta>0$ there are $\eta^*(\beta)>0$ and $c(\beta)>0$ with the following property. Let $0<\eta,\varepsilon_0<\eta^*(\beta)$ and let $Z=(X[1],X[2],X[3],Y[4],Y[5],Y[6])$ be a weighted 6-partite complex with:
--
--   1. **Local-spectral expansion:** $Z$ is a $\lambda$-product for some $0\le\lambda\le\min(1,(\varepsilon_0\eta)^{2C})$;
--   2. **Coboundary expansion:** $h^1(Y,\mathrm{Sym}(m))\ge\beta$ for every $m\le\varepsilon_0^{-C}$;
--   3. **Local soundness:** for every $s\in Y(0)\cup Y(1)$ the neighbourhood test on $X_s$ is $(\varepsilon_0',\eta',2^{-40},10)$-sound, where $\varepsilon_0'=\varepsilon_0^C$, $\eta'=(\varepsilon_0\eta)^C$;
--   4. **Intersection consistency:** for every $s\in Y(0)\cup Y(1)$ and $(u,v)\in X_s[1,3]$, $X_{uv}[2]=X_{suv}[2]$; and for every $\{y,y'\}\in Y(1)$ and $u\in X_{yy'}[1]\cup X_{yy'}[3]$, $X_{yu}[2]=X_{yy'u}[2]$.
--
--   Then the neighbourhood test on $X=(X[1],X[2],X[3])$ is
--   $$(\varepsilon_0,\ \eta,\ c(\beta),\ e)\text{-sound}.$$
--
--   This is the paper's main local-to-global agreement theorem; Theorem 6.1 obtains its sound test by verifying these four hypotheses on KMS complexes.
--
--   Differences from the source:
--   - reading: λ-local-spectral HDX (not defined in the paper) → λ-product (Definition 2.11) with 0 ≤ λ ≤ 1; reason: §2.5: 'every two-color graph in every link of Z is a λ-expander; equivalently, Z is a λ-product'; [0,1] is the range of Definition 2.11
--   - encoding: 'for every η > 0 and ε₀ > 0 sufficiently small as a function of β'; Ω_β(1); O(1) → ∃ C, ∃ e > 0, ∀ β > 0, ∃ thr > 0, ∃ c > 0, ∀ η, ε₀ ∈ (0, thr); reason: the order in which the paper fixes its constants: C and the exponent are universal, the threshold and soundness constant depend on β only
--   - encoding: faces s ∈ Y(0) ∪ Y(1) and (u, v) ∈ X_s[1, 3] → a facet y and a colour set J ⊆ {3, 4, 5} with |J| ∈ {1, 2}: s = y_J, (u, v) = (y₀, y₂); X_s is Z conditioned on x_J = y_J; reason: every such pair (s, (u, v)) occurs in a facet; same conditions
--   - reading: X_yu[2] = X_yy′u[2] for {y, y′} ∈ Y(1) → required for both endpoints (ordered pairs of distinct colours j, j′); reason: the edge {y, y′} is unordered, so either endpoint may play y
--   - encoding: m ≤ ε₀^{-C} (m a positive integer) → every natural m with m ≤ ε₀^{-C}, including m = 0; reason: Sym(0) is trivial, so the added case holds for every complex
--   - encoding: colours 1, …, 6 → Fin 6 with 0-based colours 0, …, 5; reason: Lean convention; same instances
--   - encoding: a nonempty finite alphabet Σ → a type Sig : Type with Fintype (and Nonempty where the source asks for it); reason: every finite alphabet is in bijection with a type in Type 0
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 18, Theorem 3.2

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex
import Definitions.Def_HDXNbhdPCP_Main_Agreement

namespace HDXNbhdPCP.Main

/-- Theorem 3.2 (local-to-global theorem). `Z` is 6-partite with colours `0, …, 5` (the paper's
`1, …, 6`); `X = Z[0, 1, 2]` and `Y = Z[3, 4, 5]`. A face `s ∈ Y(0) ∪ Y(1)` is `y_J` for a facet `y`
and a set `J ⊆ {3, 4, 5}` of one or two colours; the link `X_s` is `Z` conditioned on `x_J = y_J`. -/
theorem theorem_3_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, 0 < e ∧ ∀ β : ℝ, 0 < β →
    ∃ thr : ℝ, 0 < thr ∧ ∃ c : ℝ, 0 < c ∧
    ∀ η ε₀ : ℝ, 0 < η → η < thr → 0 < ε₀ → ε₀ < thr →
    ∀ (V : Fin 6 → Type) (Z : ColoredComplex (Fin 6) V), FinDist.IsProb Z →
      -- 1. local spectral expansion: `Z` is a `λ`-product with `λ ≤ (ε₀ η)^{2C}`
      (∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ lam ≤ (ε₀ * η) ^ (2 * C) ∧ Z.IsProduct lam) →
      -- 2. coboundary expansion: `h¹(Y, Sym(m)) ≥ β` for all `m ≤ ε₀^{-C}`
      (∀ m : ℕ, (m : ℝ) ≤ ε₀ ^ (-C) → Z.HasCobExpOn {3, 4, 5} (Equiv.Perm (Fin m)) β) →
      -- 3. local soundness on `X_s`, `s ∈ Y(0) ∪ Y(1)`
      (∀ J : Finset (Fin 6), J ⊆ {3, 4, 5} → 1 ≤ J.card → J.card ≤ 2 →
        ∀ y ∈ Z.supp, ((Z.condFace J y).nbhdTestOn 0 1 2).IsSound
          (ε₀ ^ C) ((ε₀ * η) ^ C) (1 / 2 ^ 40) 10) →
      -- 4a. intersection consistency: `X_{uv}[2] = X_{suv}[2]` for `(u, v) ∈ X_s[1, 3]`
      (∀ J : Finset (Fin 6), J ⊆ {3, 4, 5} → 1 ≤ J.card → J.card ≤ 2 → ∀ y ∈ Z.supp,
        Z.vertexSetGiven (fun x => x 0 = y 0 ∧ x 2 = y 2) 1 =
          Z.vertexSetGiven (fun x => (∀ i ∈ J, x i = y i) ∧ x 0 = y 0 ∧ x 2 = y 2) 1) →
      -- 4b. `X_{yu}[2] = X_{yy'u}[2]` for `{y, y'} ∈ Y(1)` and `u ∈ X_{yy'}[1] ∪ X_{yy'}[3]`
      (∀ j j' : Fin 6, j ∈ ({3, 4, 5} : Finset (Fin 6)) → j' ∈ ({3, 4, 5} : Finset (Fin 6)) →
        j ≠ j' → ∀ y ∈ Z.supp, ∀ c ∈ ({0, 2} : Finset (Fin 6)),
          Z.vertexSetGiven (fun x => x j = y j ∧ x c = y c) 1 =
            Z.vertexSetGiven (fun x => x j = y j ∧ x j' = y j' ∧ x c = y c) 1) →
      (Z.nbhdTestOn 0 1 2).IsSound ε₀ η c e := by sorry

end HDXNbhdPCP.Main
