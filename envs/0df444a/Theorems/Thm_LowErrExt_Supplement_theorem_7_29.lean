-- Prove2me | Theorems.Thm_LowErrExt_Supplement_theorem_7_29
-- name    : LowErrExt.Supplement.theorem_7_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:38:13.65264+00:00
-- url     : https://prove2.me/theorems/441b9d63-064e-408e-9736-fb79fc977ed1
-- title:
--   Theorem 7.29 — approximate duality in the high-error regime $\varepsilon>1-1/(100m^2n)$, $\ell=C\sqrt{n\log(1/\varepsilon)}$
-- statement:
--   Let $m\ge2$. There is a constant $C\ge1$ depending only on $m$ such that the following holds. Let $G,G'$ be finite abelian groups, $G$ of torsion $m$ with $n=H_0[G]$, let $S$ be a finite set, and let
--   $$\varepsilon\in\Big(1-\frac{1}{100m^2n},\,1\Big]$$
--   (the interval $(0,1]$ when $n=0$). Let $f:G\times S\to G'$ be a seeded homomorphism ($f(\cdot,y)$ is a homomorphism for every $y\in S$), $\psi:G'\to\mathbb C^\times$ a character, and $\mathbf X\sim G$, $\mathbf Y\sim S$ independent. If $|\mathbb E[\psi(f(\mathbf X,\mathbf Y))]|\ge\varepsilon$, then there are subsources $\mathbf X'\subseteq_\ell\mathbf X$ and $\mathbf Y'\subseteq_\ell\mathbf Y$ with $|\mathbb E[\psi(f(\mathbf X',\mathbf Y'))]|=1$, where
--   $$\ell=C\sqrt{n\log(1/\varepsilon)}.$$
--
--   In the nearly-dual regime the loss of approximate duality is of the conjectured optimal order $\sqrt{n\log(1/\varepsilon)}$; this is the high-error input to Theorems 1.3 and 1.4.
--
--   **Formalization Note** $\mathbf X'\subseteq_\ell\mathbf X$ means $\mathbf X'=\mathbf X|_{\mathbf X\in A}$ for some $A\subseteq\mathrm{supp}(\mathbf X)$ with $\Pr[\mathbf X\in A]\ge2^{-\ell}$ (Definition 2.2); characters are `AddChar G' ℂ`; the expectation over the independent pair is the published `pairExp`; logarithms are base 2.
--
--   Differences from the source:
--   - encoding: ε ∈ (1 − 1/(100m²n), 1], with 1 − 1/(Cn) := 0 when n = 0 (footnote 48) → lower end written as if H0[G] = 0 then 0 else 1 − 1/(100 m² H0[G]); reason: the footnote's convention made explicit; Lean's 1/0 = 0 would otherwise give the empty interval (1, 1]
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 7.29, p.71 (footnote 48, p.71)

import Mathlib
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_condOn
import Definitions.Def_LowErrExt_strongBias

namespace LowErrExt.Supplement

open LowErrExt

/-- **Theorem 7.29 (Approximate duality, high-error regime).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 7.29, p.71: "Let G, G′ be finite abelian groups such that G has torsion m ≥ 2, and H0[G] = n.
Let S be a finite set, and ε ∈ (1 − 1/(100m²n), 1]. For any seeded homomorphism f : G × S → G′,
character ψ : G′ → C^×, and independent random variables X ∼ G, Y ∼ S, the following holds. If
|E[ψ(f(X, Y))]| ≥ ε, then there exist X′ ⊆_ℓ X and Y′ ⊆_ℓ Y such that |E[ψ(f(X′, Y′))]| = 1, where
ℓ := C√(n log(1/ε)) for some constant C ≥ 1 depending only on m."

**Formalization Note.** Footnote 48 (p.71): "When n = 0, it is convenient to define this expression
as 1 − 1/(Cn) := 0", so for `n = 0` the range is `(0, 1]`. `C ≥ 1` is chosen after `m`, before
everything else (footnote 50's value is not part of the statement). A seeded homomorphism is additive
in its first argument for each seed (Definition 7.1, p.51); characters are `AddChar G′ ℂ`.
`X′ ⊆_ℓ X` (Definition 2.2, p.10) is `X|X∈A` for some `A ⊆ supp X` with `Pr[X ∈ A] ≥ 2^{−ℓ}`
(published `condOn`, `probOf`); the expectation over the independent pair is the published `pairExp`.
Logarithms are base 2. -/
theorem theorem_7_29 (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (G G' S : Type) [AddCommGroup G] [Fintype G] [AddCommGroup G'] [Fintype G'] [Fintype S],
        (∀ x : G, m • x = 0) → ∀ ε : ℝ,
          (if H0 (Set.univ : Set G) = 0 then (0 : ℝ)
            else 1 - 1 / (100 * (m : ℝ) ^ 2 * H0 (Set.univ : Set G))) < ε → ε ≤ 1 →
          ∀ f : G × S → G', (∀ (y : S) (x x' : G), f (x + x', y) = f (x, y) + f (x', y)) →
            ∀ (ψ : AddChar G' ℂ) (X : PMF G) (Y : PMF S),
              ε ≤ ‖pairExp X Y (fun x y => ψ (f (x, y)))‖ →
                ∃ (A : Set G) (B : Set S), A ⊆ X.support ∧ B ⊆ Y.support ∧
                  (2 : ℝ) ^ (-(C * Real.sqrt (H0 (Set.univ : Set G) * Real.logb 2 (1 / ε)))) ≤
                    probOf X A ∧
                  (2 : ℝ) ^ (-(C * Real.sqrt (H0 (Set.univ : Set G) * Real.logb 2 (1 / ε)))) ≤
                    probOf Y B ∧
                  ‖pairExp (condOn X A) (condOn Y B) (fun x y => ψ (f (x, y)))‖ = 1 := by sorry

end LowErrExt.Supplement
