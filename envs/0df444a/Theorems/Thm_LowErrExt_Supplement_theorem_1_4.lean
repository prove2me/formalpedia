-- Prove2me | Theorems.Thm_LowErrExt_Supplement_theorem_1_4
-- name    : LowErrExt.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:34:34.89293+00:00
-- url     : https://prove2.me/theorems/1f4047f1-05ba-420d-b886-a454b44ab5a7
-- title:
--   Theorem 1.4 — multi-regularity approximate duality over $\mathbb F_2$ with $\ell=C((tn)^C\log(1/\varepsilon))^{1/(C+1)}$
-- statement:
--   There is a universal constant $C\ge1$ such that the following holds. Let $\mathbf X,\mathbf Y$ be independent random variables on $\mathbb F_2^n$ with supports $X,Y$, let $f:\mathbb F_2^n\times\mathbb F_2^n\to\mathbb F_2^t$ be bilinear, and let $\varepsilon\in(0,1]$. Put
--   $$\ell=C\big((tn)^C\log(1/\varepsilon)\big)^{1/(C+1)}.$$
--   Then there is a finite collection $\mathcal P$ of pairwise disjoint product sets $P=X'\times Y'\subseteq X\times Y$ such that
--
--   1. for every $P\in\mathcal P$ and every linear $\psi:\mathbb F_2^t\to\mathbb F_2$, either $\mathrm{bias}[\psi(f(\mathbf X,\mathbf Y)|_{(\mathbf X,\mathbf Y)\in P})]=1$ (structure) or $\mathrm{bias}[\psi(f(\mathbf X,\mathbf Y)|_{(\mathbf X,\mathbf Y)\in P})]<\varepsilon$ (randomness);
--   2. $\Pr[(\mathbf X,\mathbf Y)\in P]\ge2^{-\ell}$ for every $P\in\mathcal P$;
--   3. $\Pr[(\mathbf X,\mathbf Y)\notin\bigcup\mathcal P]<\varepsilon$.
--
--   This regularity version of approximate duality tiles two independent sources by product blocks on which every parity of $f$ is constant or nearly unbiased; it is the step that turns two independent sources into an affine source in the two-source extractor.
--
--   **Formalization Note** On a product block, $(\mathbf X,\mathbf Y)$ conditioned on $P=X'\times Y'$ is the independent pair $(\mathbf X|_{\mathbf X\in X'},\mathbf Y|_{\mathbf Y\in Y'})$; the bias of a bit is `bitBias`; bilinearity is the published `IsBilinear`; logarithms are base 2.
--
--   Differences from the source:
--   - encoding: ε unrestricted (log(1/ε) in ℓ) → ε ∈ (0, 1]; reason: ℓ is a real power of t^C n^C log(1/ε), defined only when log(1/ε) ≥ 0, i.e. ε ≤ 1; ε > 0 for log(1/ε)
--   - encoding: collection 𝒫 of disjoint subsets X′ × Y′ → a Finset of pairs (X′, Y′) of finite sets, with pairwise disjoint products; reason: the supports are finite, so every collection is a finite set of pairs; a block of positive mass determines its pair
--   - encoding: (X, Y)|_{(X,Y)∈P} → the independent pair (condOn X X′, condOn Y Y′); reason: X, Y are independent and P is a product set, so conditioning on P conditions each coordinate; Pr[P] ≥ 2^{−ℓ} > 0
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 1.4, p.7

import Mathlib
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_LowErrExt_condOn
import Definitions.Def_LowErrExt_IsTwoSourceRankExt
import Definitions.Def_LowErrExt_Supplement_setBias

namespace LowErrExt.Supplement

open LowErrExt

/-- **Theorem 1.4 (Multi-regularity approximate duality).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 1.4, p.7: "Let X, Y ∼ F₂ⁿ be independent random variables with supports X, Y (respectively),
and let f : F₂ⁿ × F₂ⁿ → F₂ᵗ be a bilinear map. Then, there exists a collection 𝒫 of disjoint subsets
X′ × Y′ ⊆ X × Y such that for every P ∈ 𝒫 and linear function ψ : F₂ᵗ → F₂, either:
bias[ψ(f(X, Y)|_{(X,Y)∈P})] = 1, or (structure) bias[ψ(f(X, Y)|_{(X,Y)∈P})] < ε. (randomness)
Crucially, we also have that Pr[(X, Y) ∈ P] ≥ 2^{−ℓ} for every P ∈ 𝒫, and Pr[(X, Y) ∉ 𝒫] < ε, where
ℓ := C((tn)^C log(1/ε))^{1/(C+1)} for some universal constant C ≥ 1."

**Formalization Note.** The collection `𝒫` is the finite set `Parts`. `C ≥ 1` is universal (chosen before `n, t, X, Y, f, ε`); `ε ∈ (0, 1]`, the
range on which `ℓ` is defined (`log(1/ε) ≥ 0`). A block `P = X′ × Y′` is a pair of finite sets
`(P.1, P.2)` inside the supports; blocks are pairwise disjoint as product sets. Since `X, Y` are
independent and `P` is a product, `(X, Y)|_{(X,Y)∈P}` is the independent pair
`(X|X∈X′, Y|Y∈Y′)` (`condOn`, published), well defined because `Pr[(X, Y) ∈ P] ≥ 2^{−ℓ} > 0`.
`ψ` ranges over all `𝔽₂`-linear maps `𝔽₂ᵗ → 𝔽₂` (including `ψ = 0`); `bias` of a bit is
`bitBias`. `Pr[(X, Y) ∉ 𝒫]` is the mass outside the union of the blocks. `f` bilinear is the
published `IsBilinear`. Logarithms are base 2. -/
theorem theorem_1_4 :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n t : ℕ) (X Y : PMF (Fin n → ZMod 2))
        (f : (Fin n → ZMod 2) → (Fin n → ZMod 2) → (Fin t → ZMod 2)), IsBilinear f →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∃ Parts : Finset (Finset (Fin n → ZMod 2) × Finset (Fin n → ZMod 2)),
            (∀ P ∈ Parts, (↑P.1 : Set (Fin n → ZMod 2)) ⊆ X.support ∧
              (↑P.2 : Set (Fin n → ZMod 2)) ⊆ Y.support) ∧
            (∀ P ∈ Parts, ∀ Q ∈ Parts, P ≠ Q → Disjoint (P.1 ×ˢ P.2) (Q.1 ×ˢ Q.2)) ∧
            (∀ P ∈ Parts, ∀ ψ : (Fin t → ZMod 2) →ₗ[ZMod 2] ZMod 2,
              bitBias ((indepPair (condOn X ↑P.1) (condOn Y ↑P.2)).map
                  (fun z => ψ (f z.1 z.2))) = 1 ∨
              bitBias ((indepPair (condOn X ↑P.1) (condOn Y ↑P.2)).map
                  (fun z => ψ (f z.1 z.2))) < ε) ∧
            (∀ P ∈ Parts,
              (2 : ℝ) ^ (-(C * (((t : ℝ) * n) ^ C * Real.logb 2 (1 / ε)) ^ (1 / (C + 1)))) ≤
                probOf (indepPair X Y) ↑(P.1 ×ˢ P.2)) ∧
            probOf (indepPair X Y) {z | ∀ P ∈ Parts, z ∉ P.1 ×ˢ P.2} < ε := by sorry

end LowErrExt.Supplement
