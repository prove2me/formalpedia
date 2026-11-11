-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_theorem_6_2
-- name    : MatchIndiff.PublicSM.theorem_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:26:45.233193+00:00
-- url     : https://prove2.me/theorems/7c15ae83-50fd-497a-bf16-29db11f82160
-- title:
--   Theorem 6.2 — verifying the canonical strongly or super-stable matching under public priorities takes k(k − 1) bits at a strict complete Q_k, and Θ(n²) bits in general
-- statement:
--   Consider public-priority one-to-one school choice with weak (tied) student rows, the canonical selectors $\Phi_s$ (strong) and $\Phi_u$ (super), and joint verification with rank outputs (IJVC) or exact outputs (EJVC).
--
--   1. For every even $k\ge2$ there is a fixed, strict, complete public priority profile $Q_k$ on $3k$ students and $3k$ schools such that, for every public student and school order, on the unrestricted student report domain
--   $$\mathrm{IJVC}_{Q_k}(\Phi_\alpha)\ge k(k-1)\quad\text{and}\quad\mathrm{EJVC}_{Q_k}(\Phi_\alpha)\ge k(k-1)\qquad(\alpha\in\{s,u\}).$$
--   2. These lower bounds already hold on a product domain $\prod_i D_i$ of student rows with fixed student acceptability (all rows in $D_i$ have the same acceptable set) in which every profile has a super-stable matching (at the same $Q_k$).
--   3. Consequently both unrestricted joint-verification complexities are $\Theta(n^2)$ for both canonical selectors: there are constants $c,C>0$ and $N$ such that for every $n\ge N$, some public input with $n$ students and $n$ schools has $\mathrm{JVC}\ge cn^2$, and every public input with $n$ students and $n$ schools (priorities possibly tied and incomplete) has $\mathrm{JVC}\le Cn^2$.
--
--   Publishing a matching certifies stability but not the canonical selection; the theorem shows that certifying the canonical rank-optimal outcome costs quadratically many bits even when priorities are strict and public, acceptability is fixed and a super-stable matching always exists.
--
--   **Formalization Note.** `JVCge ξ α b Dom K` and `JVCle ξ α b Dom K` (Protocol) express $\mathrm{JVC}\ge K$ and $\mathrm{JVC}\le K$; clause 3 is written with explicit protocols and real constants.
--
--   Differences from the source:
--   - generalization: IJVC_{Q_k}(Φ_α) ≥ k(k − 1) (only Q fixed by the subscript, a supremum over the other public data) → the bound at every public input (Q_k, ρ, τ), for every public student order ρ and school order τ; reason: the proof works for every order (Lemma 6.3); the bound at every ξ implies the paper's bound on the supremum, so the statement specializes to the source
--   - reading: JVC ≥ K and JVC ≤ K (minimum of ⌈log₂|C|⌉ over complete and sound protocols) → every complete and sound protocol has Nat.clog 2 c ≥ K; some protocol has Nat.clog 2 c ≤ K; reason: the minimum written without an infimum, so no empty-set default value enters
--   - reading: unrestricted complexities are Θ(n²) (supremum over Ξ_{n,n}) → ∃ c C > 0, N such that for all n ≥ N: some valid ξ has every protocol of cost ≥ c n², and every valid ξ has a protocol of cost ≤ C n²; one pair of constants for both selectors and both output types; reason: Ξ_{n,n} is finite so the supremum is attained; uniform constants are the min/max over the four cases
--   - reading: a product domain with fixed student acceptability → D : Fin (3k) → Set of valid rows, all rows of D i with the same acceptable schools, the domain Set.pi univ D; reason: the paper's description of the domain
--   - encoding: α ∈ {s, u}, output type b ∈ {I, E}, board alphabet C → α : StabKind with α ≠ weak, b : OutKind, board alphabet Fin c with cost Nat.clog 2 c; reason: Lean convention
--   - encoding: students N, schools H, weak rows, ⊥ with rank m + 1 → Fin n, Fin m, rows r : Fin k → ℕ with IsRow (0 = unacceptable, j = j-th tie class), rk with ⊥ ↦ k + 1 and unacceptable ↦ k + 2, matchings with Option values; reason: Lean convention; the gap-free row encoding is a bijection with the paper's rows and rk orders partners exactly as the paper does
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 10, Theorem 6.2

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model
import Definitions.Def_MatchIndiff_PublicSM_Protocol

namespace MatchIndiff.PublicSM

/-- Theorem 6.2 (p. 10): (1) for every even `k ≥ 2` there is a strict, complete public priority
profile `Q_k` on `3k` students and `3k` schools at which, for every public student and school
order, rank and exact joint verification of `Φ_s` and `Φ_u` need at least `k(k - 1)` bits;
(2) the same bound holds on a product domain of student rows with fixed acceptability on which
every profile has a super-stable matching; (3) the unrestricted complexities are `Θ(n²)`. -/
theorem theorem_6_2 :
    (∀ k : ℕ, 2 ≤ k → Even k →
      ∃ Q : Fin (3 * k) → Fin (3 * k) → ℕ,
        (∀ h, IsRow (Q h)) ∧ (∀ h d, Q h d ≠ 0) ∧ (∀ h d e, Q h d = Q h e → d = e) ∧
        (∀ (ρ τ : Fin (3 * k) ≃ Fin (3 * k)) (α : StabKind), α ≠ StabKind.weak →
          ∀ b : OutKind, JVCge ⟨Q, ρ, τ⟩ α b (fullDomain (3 * k) (3 * k)) (k * (k - 1))) ∧
        ∃ D : Fin (3 * k) → Set (Fin (3 * k) → ℕ),
          (∀ i, ∀ r ∈ D i, IsRow r) ∧
          (∀ i, ∀ r ∈ D i, ∀ r' ∈ D i, ∀ h, r h = 0 ↔ r' h = 0) ∧
          (∀ P : Fin (3 * k) → Fin (3 * k) → ℕ, (∀ i, P i ∈ D i) →
            ∃ μ : Matching (3 * k) (3 * k), IsStable StabKind.super P Q μ) ∧
          (∀ (ρ τ : Fin (3 * k) ≃ Fin (3 * k)) (α : StabKind), α ≠ StabKind.weak →
            ∀ b : OutKind, JVCge ⟨Q, ρ, τ⟩ α b (Set.pi Set.univ D) (k * (k - 1)))) ∧
    (∃ (c C : ℝ) (N : ℕ), 0 < c ∧ 0 < C ∧
      ∀ n : ℕ, N ≤ n → ∀ α : StabKind, α ≠ StabKind.weak → ∀ b : OutKind,
        (∃ ξ : PublicInput n n, ξ.Valid ∧
          ∀ (cc : ℕ) (p : VerifProtocol (fun _ : Fin n => Fin n → ℕ) (fun _ : Fin n => Out n b)
            (Fin cc)), IsPublicJV ξ α b (fullDomain n n) p → c * (n : ℝ) ^ 2 ≤ (Nat.clog 2 cc : ℝ)) ∧
        (∀ ξ : PublicInput n n, ξ.Valid →
          ∃ (cc : ℕ) (p : VerifProtocol (fun _ : Fin n => Fin n → ℕ) (fun _ : Fin n => Out n b)
            (Fin cc)), IsPublicJV ξ α b (fullDomain n n) p ∧ (Nat.clog 2 cc : ℝ) ≤ C * (n : ℝ) ^ 2)) := by sorry

end MatchIndiff.PublicSM
