-- Prove2me | Theorems.Thm_LowErrExt_theorem_7_5
-- name    : LowErrExt.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:09.167277+00:00
-- url     : https://prove2.me/theorems/eb9e0f44-00b6-41cb-adc6-5b6e8bbfb119
-- title:
--   Theorem 7.5 — multi-regularity approximate duality, with robustness and strength
-- statement:
--   Let $m\ge2$. There is a constant $C\ge1$ depending only on $m$ such that the following holds. Let $G,G'$ be finite abelian groups with $G$ of torsion $m$, $n:=H_0[G]$, $t:=H_0[G']$, let $S$ be a finite set and $\varepsilon\in(0,1]$. Let $f:G\times S\to G'$ be a seeded homomorphism ($f(\cdot,y)$ is a homomorphism for every $y$), and let $\mathbf X$, $\mathbf Y$ be independent sources on $G$, $S$. Then there is a three-round communication protocol $\Gamma:G\times S\to\Sigma$ such that
--   $$\Pr_{\gamma\sim\Gamma(\mathbf X,\mathbf Y)}\big[f\text{ is }\varepsilon\text{-robustly and strongly }\varepsilon\text{-regular on }(\mathbf X,\mathbf Y)|_{\Gamma(\mathbf X,\mathbf Y)=\gamma}\big]\ge1-\varepsilon,$$
--   where
--   $$H_0[\Sigma]\le\ell:=C\big(t^{C+1}n^{2C}\log(2/\varepsilon)\big)^{1/(2C+1)}+Ct .$$
--
--   Regularity is with respect to every character of $G'$ at once, on the same parts. This is the central result of §7, of which Theorem 5.2 is a special case.
--
--   Differences from the source:
--   - encoding: G has torsion m → m • x = 0 for every x ∈ G; reason: the paper's meaning of bounded torsion (footnote 20, p.40); same instances
--   - encoding: Γ : G × S → Σ a three-round protocol, H0[Σ] → Γ : G × S → Σ₁ × Σ₂ × Σ₃ with finite Σᵢ, H0[Σ] = log₂(|Σ₁||Σ₂||Σ₃|); reason: Definition 2.22's shape of an r-round protocol
--   - encoding: (X, Y)|Γ(X,Y)=γ and Pr over γ ∼ Γ(X, Y) → the independent pair (X | A_γ, Y | B_γ) for the two sides of the fiber, with probability over (x, y) ∼ (X, Y) and γ = Γ(x, y); reason: a protocol is a product partition, so the fiber is A_γ × B_γ and the conditioned pair is independent with these marginals
--   - encoding: characters ψ : G′ → ℂ^×; subsources X′ ⊆_{log(1/ε)} X → AddChar G′ ℂ; events of probability at least ε; reason: same objects (Definition 2.2 with ℓ = log(1/ε))
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 7.5, p.52

import Mathlib
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_LowErrExt_condOn
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_IsRobStrongRegular
import Definitions.Def_LowErrExt_IsProductPartition
import Definitions.Def_LowErrExt_IsProtocol3

namespace LowErrExt

/-- **Theorem 7.5 (Multi-regularity approximate duality, with robustness and strength).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 7.5, p.52: "Let G, G′ be finite abelian groups such that G has torsion m ≥ 2, H0[G] = n, and
H0[G′] = t. Let S be a finite set, and let ε ∈ (0, 1]. For any seeded homomorphism f : G × S → G′
and independent random variables X ∼ G, Y ∼ S, there exists a three-round communication protocol
Γ : G × S → Σ such that Pr_{γ∼Γ(X,Y)}[f is ε-robustly and strongly ε-regular on (X, Y)|Γ(X,Y)=γ]
≥ 1 − ε, where H0[Σ] ≤ ℓ := C(t^{C+1}n^{2C} log(2/ε))^{1/(2C+1)} + Ct for some constant C ≥ 1
depending only on m."

**Formalization Note.** `C` is chosen after `m` and before everything else. `Σ = Σ₁ × Σ₂ × Σ₃` with
finite rounds' alphabets (Definition 2.22), and `H0[Σ] = log₂(|Σ₁||Σ₂||Σ₃|)`. A protocol is a product
partition, so for `γ = Γ(x, y)` the conditioned pair `(X, Y)|Γ(X,Y)=γ` is the independent pair
`(X | X ∈ fiberLeft Γ γ, Y | Y ∈ fiberRight Γ γ)`; the probability is over `(x, y) ∼ (X, Y)`.
A seeded homomorphism is additive in its first argument for each seed (Definition 7.1, p.51). -/
theorem theorem_7_5 (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (G G' S : Type) [AddCommGroup G] [Fintype G] [AddCommGroup G'] [Fintype G'] [Fintype S],
        (∀ x : G, m • x = 0) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∀ f : G × S → G', (∀ (y : S) (x x' : G), f (x + x', y) = f (x, y) + f (x', y)) →
            ∀ (X : PMF G) (Y : PMF S),
              ∃ (S₁ S₂ S₃ : Type) (_ : Fintype S₁) (_ : Fintype S₂) (_ : Fintype S₃)
                (Γ : G × S → S₁ × S₂ × S₃),
                IsProtocol3 Γ ∧
                Real.logb 2 ((Fintype.card S₁ * Fintype.card S₂ * Fintype.card S₃ : ℕ) : ℝ) ≤
                  C * (H0 (Set.univ : Set G') ^ (C + 1) * H0 (Set.univ : Set G) ^ (2 * C) *
                      Real.logb 2 (2 / ε)) ^ (1 / (2 * C + 1)) + C * H0 (Set.univ : Set G') ∧
                1 - ε ≤ probOf (indepPair X Y)
                  {z | IsRobStrongRegular ε ε f (condOn X (fiberLeft Γ (Γ z)))
                        (condOn Y (fiberRight Γ (Γ z)))} := by sorry

end LowErrExt
