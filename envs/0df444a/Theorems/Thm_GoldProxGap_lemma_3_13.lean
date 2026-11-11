-- Prove2me | Theorems.Thm_GoldProxGap_lemma_3_13
-- name    : GoldProxGap.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:22:58.619875+00:00
-- url     : https://prove2.me/theorems/e2dd53d0-76ea-4b10-9cc2-26ba5cbf79e8
-- title:
--   Lemma 3.13 — two individually far inputs: $\mathrm{agr}_K(f)\le(b+1)K/2-1$, $\mathrm{agr}_K(g)=\mathrm{CA}_K(f,g)=K$, and the binary padding bound
-- statement:
--   **Lemma 3.13 (Two individually far inputs).** Let $b$ be a prime power (a power of the characteristic), let $\mathbb F\supseteq\mathbb F_b$ be finite, and let $D\subseteq\mathbb F$ be an affine $\mathbb F_b$-space of size $N=b^d$ with $d\ge3$. Put $K=N/b^2$, $\lambda=L_D'$ and $R=(L_D-\lambda X)^{1/b}$. For any $\beta\in\mathbb F\setminus D$ the pair
--   $$
--   f(x)=\frac{(-\lambda(x-\beta))^{1/b}}{x-\beta},\qquad g(x)=\frac1{x-\beta}
--   $$
--   satisfies
--   $$
--   \mathrm{agr}_K(f)\le\frac{(b+1)K}2-1,\qquad \mathrm{agr}_K(g)=\mathrm{CA}_K(f,g)=K .
--   $$
--   Replacing the first word $R(x)/(x-\beta)$ of Lemma 3.11 by $f$ translates the challenge set by $-(\lambda\beta)^{1/b}$: for every $T$, $\mathrm{Bad}_T(f,g)=\mathrm{Bad}_T(R/(x-\beta),g)-(\lambda\beta)^{1/b}$, so the number of exceptional challenges is unchanged, and $0$ is not exceptional when $T\ge(b+1)K/2$.
--
--   For $b=2$, $f(x)=\sqrt{\lambda/(x-\beta)}$ and the bound is $\mathrm{agr}_K(f)\le 3N/8-1$. In this binary case, for every polynomial $A$ of degree $w$ with $A(\beta)\ne0$ and $3w\le K-1$, the padded pair satisfies $\mathrm{agr}_K(Af)\le\lfloor(3K+w-1)/2\rfloor$ and $\mathrm{agr}_K(Ag)=\mathrm{CA}_K(Af,Ag)=K$.
--
--   The lemma makes the first input individually far from the code without changing the exceptional set, so that zero is not an exceptional challenge.
--
--   **Formalization Note** $\mathbb F$ has prime characteristic $p$ and $b=p^k$ with $k\ge1$; $\mathbb F_b$ is a subfield with $b$ elements and $D=a+V$ for an $\mathbb F_b$-submodule $V$ with $b^d$ elements. $c^{1/b}$ is the inverse Frobenius power, $\lambda$ the coefficient of $X$ in $L_D$. The binary clauses are stated under $p^k=2$.
--
--   Differences from the source:
--   - encoding: b a prime power, a power of the characteristic (p.22), F ⊇ F_b → b = p^k with p the prime characteristic of F and k ≥ 1, and a subfield Fb ⊆ F with b elements; reason: a prime power b with F_b ⊆ F is a power of the characteristic
--   - encoding: affine F_b-space D of size b^d → D = a + V for a ∈ F and an Fb-submodule V of F with b^d elements; reason: Definition 3.7
--   - encoding: translates its challenge set by −(λβ)^{1/b} → for every T, Bad_T(f, g) is the image of Bad_T(R/(x − β), g) under z ↦ z − (λβ)^{1/b}, and the two sets have the same size; reason: same claim
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 3.13, p.23 (and the paragraph before it, p.22)

import Mathlib
import Definitions.Def_GoldProxGap_reedSolomon
import Definitions.Def_GoldProxGap_domainFinset
import Definitions.Def_GoldProxGap_locator

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Lemma 3.13 (Two individually far inputs)**, p.23. Dao, Kominers, Thaler, Zheng,
*Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission
manuscript (2 November 2026, sha256 6c2d9ced…).

"Let b be a prime power, let F ⊇ F_b be finite, and let D ⊆ F be an affine F_b-space of size
N = b^d, with d ≥ 3. Put K = N/b², λ = L′_D, and R = (L_D − λX)^{1/b}. For any β ∈ F \ D, the pair
f(x) = (−λ(x − β))^{1/b}/(x − β), g(x) = 1/(x − β) satisfies agr_K(f) ≤ (b + 1)K/2 − 1,
agr_K(g) = CA_K(f, g) = K. Replacing the first word of Lemma 3.11, with this R, by f translates its
challenge set by −(λβ)^{1/b}. The number of exceptional challenges is unchanged, and zero is not
exceptional when T ≥ (b + 1)K/2. For b = 2, the first input is f(x) = √(λ/(x − β)) and its bound
is 3N/8 − 1. In this binary case, let A be any polynomial of degree w with A(β) ≠ 0 and
3w ≤ K − 1. At the same message length K, the padded pair also satisfies
agr_K(Af) ≤ ⌊(3K + w − 1)/2⌋, agr_K(Ag) = CA_K(Af, Ag) = K."

**Formalization Note.**
* The text before the lemma (p.22) fixes that `b` is a power of the characteristic: here `F` has
  characteristic a prime `p` and `b = p ^ k` with `k ≥ 1`. `F ⊇ F_b` is a subfield `Fb` with `b`
  elements; the affine `F_b`-space is `D = a + V` for an `Fb`-submodule `V` of `F` with `b ^ d`
  elements.
* `c^{1/b}` is `frobRoot F p k c` (inverse of `x ↦ x^b`); `R = polyRoot p k (L_D − λX)`;
  `λ = locLam D`, the coefficient of `X` in `L_D` (the constant `L′_D`).
* "Replacing the first word of Lemma 3.11, with this R, by f": the word of Lemma 3.11 is
  `f₀(x) = R(x)/(x − β)`, and for every threshold `T`,
  `Bad_T(f, g) = Bad_T(f₀, g) − (λβ)^{1/b}`.
* The binary clauses are stated under `p ^ k = 2`, where `frobRoot F p k` is the square root. The
  padded words are `x ↦ A(x) f(x)` and `x ↦ A(x) g(x)`; `w` is `natDegree A`. -/
theorem lemma_3_13 {F : Type} [Field F] [Fintype F] (p k : ℕ) [Fact p.Prime] [CharP F p]
    (hk : 1 ≤ k) (Fb : Subfield F) (hFb : Nat.card Fb = p ^ k) (V : Submodule Fb F) (a : F)
    (d : ℕ) (hd : 3 ≤ d) (hV : Nat.card V = (p ^ k) ^ d) (β : F)
    (hβ : β ∉ translateDomain a (Finset.univ.filter (fun x => x ∈ V))) :
    let b := p ^ k
    let D : Finset F := translateDomain a (Finset.univ.filter (fun x => x ∈ V))
    let N := D.card
    let K := N / b ^ 2
    let lam := locLam D
    let R := polyRoot p k (locator D - C lam * X)
    let f : D → F := fun x => frobRoot F p k (-lam * ((x : F) - β)) / ((x : F) - β)
    let g : D → F := fun x => 1 / ((x : F) - β)
    let f₀ : D → F := fun x => R.eval (x : F) / ((x : F) - β)
    let s := frobRoot F p k (lam * β)
    (agr D K f : ℝ) ≤ ((b : ℝ) + 1) * K / 2 - 1 ∧
    agr D K g = K ∧ CA D K f g = K ∧
    (∀ T : ℕ, Bad D K T f g = (Bad D K T f₀ g).image (fun z => z - s) ∧
      (Bad D K T f g).card = (Bad D K T f₀ g).card) ∧
    (∀ T : ℕ, ((b : ℝ) + 1) * K / 2 ≤ T → (0 : F) ∉ Bad D K T f g) ∧
    (b = 2 →
      (∀ x : D, f x = frobRoot F p k (lam / ((x : F) - β))) ∧
      agr D K f ≤ 3 * N / 8 - 1 ∧
      ∀ A : F[X], A.eval β ≠ 0 → 3 * A.natDegree ≤ K - 1 →
        agr D K (fun x => A.eval (x : F) * f x) ≤ (3 * K + A.natDegree - 1) / 2 ∧
        agr D K (fun x => A.eval (x : F) * g x) = K ∧
        CA D K (fun x => A.eval (x : F) * f x) (fun x => A.eval (x : F) * g x) = K) := by sorry

end GoldProxGap
