-- Prove2me | Theorems.Thm_MulticlassOmni_Lipschitz_lemma_4_3
-- name    : MulticlassOmni.Lipschitz.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:12:12.89117+00:00
-- url     : https://prove2.me/theorems/556fe353-ec38-4932-8b52-5652391d90bf
-- title:
--   Lemma 4.3 — hard losses are bounded proper; $f_\beta(x_i)$ is Bayes-optimal with conditional regret $\ge\eta\,\mathbf 1\{a_\pi(r)\ne a^\star_i\}\ge0$
-- statement:
--   Let $C_{\mathrm{pack}}>0$ be the packing constant. There is $c>0$ such that, for every integer $k\ge3$, every $0<\varepsilon<c/(k\log(k+1))$, with $\eta=8\sqrt{k\varepsilon\log(1/\varepsilon)}$, for every Section 4.1 domain $x_1,\dots,x_N$ (`IsSection41Packing Cpack k η x`) and every tie-breaking order ($A$ first, then the $B_i$ by a permutation $\sigma$):
--   1. $L_{\mathrm{hard}}\subseteq L_{\mathrm{proper}}$: every $\ell^{\mathrm{hard}}_\pi$ is proper with values in $[0,1]$ on $\Delta_k$;
--   2. for every $i$, $b\in\{0,1\}$, $\beta\in\{1,2\}$ and $\pi:X\to\{0,1\}$ with $b=\beta-1$ whenever $\pi(x_i)=1$, writing $a^\star_i=a_\pi(f_\beta(x_i))$: $f_\beta(x_i)$ is a Bayes-optimal report for $\ell^{\mathrm{hard}}_\pi$ under $q_b(x_i)$ (its expected loss is at most that of every $r\in\Delta_k$), and every $r\in\Delta_k$ satisfies
--   $$\mathbb E_{y\sim q_b(x_i)}\big[\ell^{\mathrm{hard}}_\pi(r,y)-\ell^{\mathrm{hard}}_\pi(f_\beta(x_i),y)\big]\ge\eta\,\mathbf 1\{a_\pi(r)\ne a^\star_i\}\ge0.\qquad(25)$$
--
--   Differences from the source:
--   - generalization: the construction uses the packing of Lemma B.2 with that lemma's absolute constant C_pack → the statement holds for every C_pack > 0 (∀ C_pack > 0 before the existential constants, which may depend on it); the domain is any truncation of any set satisfying Lemma B.2's conclusion at scale 16η/125 with that C_pack; reason: instantiating C_pack with Lemma B.2's constant gives the source's statement for the source's construction
--   - generalization: ties in a_π broken by a fixed action ordering with A first → every ordering with A first and the B_i ordered by an arbitrary permutation σ (∀ σ); reason: the source's fixed ordering is one such σ
--   - encoding: 'for sufficiently small absolute c > 0' → ∃ c > 0; reason: the hypothesis ε < c/(k log(k+1)) is monotone in c, so a working c makes every smaller c work
--   - encoding: the domain X = {x_1, …, x_N} and functions π, θ : X → {0, 1} → an injective enumeration x : Fin N → ℝ^k and π, θ : Fin N → Fin 2 (π i is π(x_{i+1})); reason: same objects, indexed
--   - encoding: β ∈ {1, 2} and the hypothesis 'b = β − 1 if π(x_i) = 1' → β : ℕ with β = 1 ∨ β = 2, and π i = 1 → (b : ℕ) = β − 1; bench x β i is f_β(x_i); reason: same instances (β ≥ 1, so the natural-number subtraction is exact)
--   - encoding: a loss ℓ : Δ_k × [k] → ℝ and properness E_{y∼q}ℓ(q,y) ≤ E_{y∼q}ℓ(r,y) → a total ℓ : ℝ^k → Fin k → ℝ constrained only on stdSimplex; properness is the published UCalibDirichlet.IsProperLoss of its EReal embedding, extended by 0 off the simplex; reason: values off the simplex are never read; for real values the predicate's 'never −∞' clause is automatic, so the instances are the same
--   - encoding: labels [k] = {1, …, k} → Fin k, the source label y is the index y − 1 (label 1 is index 0); reason: relabeling; same instances
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), Lemma 4.3, p. 17

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses
import Definitions.Def_MulticlassOmni_Lipschitz_Packings
import Definitions.Def_MulticlassOmni_Lipschitz_Construction

namespace MulticlassOmni.Lipschitz

/-- **Lemma 4.3 (Conditional regret for the non-Lipschitz construction)**, Hu, Luo, Schneider,
Yang (2026), p. 17. For the packing constant `Cpack > 0` of Lemma B.2 there is `c > 0` such that
for every integer `k ≥ 3`, every `0 < ε < c/(k log(k+1))`, `η = 8√(kε log(1/ε))` and the
Section 4.1 domain `x_1, …, x_N`, and every tie-breaking order (A first, then the `B_i` by `σ`):
`L_hard ⊆ L_proper`; and for every `i`, `b ∈ {0, 1}`, `β ∈ {1, 2}` and `π : X → {0, 1}` with
`π(x_i) = 1 → b = β - 1`, writing `a*_i := a_π(f_β(x_i))`, the report `f_β(x_i)` is Bayes-optimal
for `ℓ^hard_π` under `q_b(x_i)`, and every `r ∈ Δ_k` satisfies
`E_{y∼q_b(x_i)}[ℓ^hard_π(r, y) - ℓ^hard_π(f_β(x_i), y)] ≥ η 1{a_π(r) ≠ a*_i} ≥ 0` (25). -/
theorem lemma_4_3 :
    ∀ Cpack : ℝ, 0 < Cpack → ∃ c : ℝ, 0 < c ∧
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε < c / ((k : ℝ) * Real.log ((k : ℝ) + 1)) →
        ∀ (N : ℕ) (x : Fin N → Fin k → ℝ), IsSection41Packing Cpack k (eta k ε) x →
          ∀ σ : Equiv.Perm (Fin N),
            (∀ π : Fin N → Fin 2, IsBoundedProper (hardLoss x (eta k ε) π σ)) ∧
            ∀ (i : Fin N) (b : Fin 2) (β : ℕ) (π : Fin N → Fin 2),
              (β = 1 ∨ β = 2) → (π i = 1 → (b : ℕ) = β - 1) →
                (∀ r ∈ stdSimplex ℝ (Fin k),
                  expect (qLip x (eta k ε) b i)
                      (hardLoss x (eta k ε) π σ (bench x β i)) ≤
                    expect (qLip x (eta k ε) b i) (hardLoss x (eta k ε) π σ r)) ∧
                ∀ r ∈ stdSimplex ℝ (Fin k),
                  eta k ε * (if aSel x (eta k ε) π σ r ≠ aSel x (eta k ε) π σ (bench x β i)
                      then 1 else 0) ≤
                    expect (qLip x (eta k ε) b i)
                      (fun y => hardLoss x (eta k ε) π σ r y -
                        hardLoss x (eta k ε) π σ (bench x β i) y) ∧
                  0 ≤ eta k ε * (if aSel x (eta k ε) π σ r ≠ aSel x (eta k ε) π σ (bench x β i)
                      then 1 else 0) := by sorry

end MulticlassOmni.Lipschitz
