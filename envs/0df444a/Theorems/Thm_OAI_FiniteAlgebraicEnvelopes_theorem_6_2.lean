-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_theorem_6_2
-- name    : OAI.FiniteAlgebraicEnvelopes.theorem_6_2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-14T09:27:20.641848+00:00
-- url     : https://prove2.me/theorems/efb142d0-8b4b-4f2b-9996-9945acd55866
-- title:
--   Theorem 6.2 (finite algebraic envelopes): the coding monoids $K, H$
-- statement:
--   **Theorem 6.2** of OpenAI's "Finite algebraic envelopes and the Boone-Higman conjecture" preprint (Section 6, proved in Section 7 using the finite compiler of Appendix A). Given a finitely generated group $\hat G$ with decidable word problem, there exist a finitely presented monoid $K$ with zero $\Omega \neq 1_K$, and a finitely generated monoid $H$ with decidable word problem and zero $\zeta \neq 1_H$, such that:
--
--   (i) there is an injective group homomorphism $\hat G \to H^\times$;
--
--   (ii) for the monoid $T = (K \setminus \{\Omega\}) \times P \sqcup \{0_T\}$ of Lemma 6.1 (`Definitions.Def_BooneHigman_TMonoid`), there is an injective unital monoid homomorphism $\kappa : T \to H$ with $\kappa(0_T) = \zeta$;
--
--   (iii) for every finite ordered tuple $h_1, \ldots, h_d$ of distinct nonzero elements of $H$ ($d \geq 1$), there are $L, R \in H$ with $L h_1 R = 1_H$ and $L h_i R = \zeta$ for $2 \le i \le d$;
--
--   (iv) there is an injective multiplicative (not necessarily unital) map $c : H \to K$ whose image avoids $\{1_K, \Omega\}$;
--
--   (v) there is a separator $z \in H$ such that $(\tau, \tau') \mapsto \kappa(\tau) z \kappa(\tau')$ is injective from $(T \setminus \{0_T\})^2$ into $H \setminus \{\zeta\}$.
--
--   This is the technical monoid-coding engine underlying the paper's Theorem 2.2 (the algebraic envelope construction for the Boone-Higman conjecture): $\hat G$ is any finitely generated group with decidable word problem, $H$ supplies the 'coding' monoid whose contracted monoid algebra $k_0[H]$ becomes the simple algebra $A_0$, and $K$ supplies the finitely presented monoid whose contracted monoid algebra $k_0[K]$ becomes the finitely presented algebra $B$ of Theorem 2.2 (Section 6.2). The theorem's own proof (Section 7, Appendix A) is a self-referential finite-compiler construction via Kleene's Recursion Theorem over bounded-length word rewriting — a separate, much larger piece of computability theory from the mechanical algebra of Sections 4 and 6.2-6.4, and is recorded here as an Open leaf in the dependency graph rather than attempted.
-- source:
--   OpenAI, "Finite algebraic envelopes and the Boone-Higman conjecture", OpenAI Math Release, 2026-09-23, Section 6, Theorem 6.2 (statement; proved in Section 7 via Appendix A's finite compiler).

import Mathlib
import Definitions.Def_BooneHigman
import Definitions.Def_BooneHigman_MonoidWordProblem
import Definitions.Def_BooneHigman_PMonoid
import Definitions.Def_BooneHigman_TMonoid

open OAI.FiniteAlgebraicEnvelopes

universe u

theorem OAI.FiniteAlgebraicEnvelopes.theorem_6_2 {Ghat : Type u} [Group Ghat] [Group.FG Ghat]
    (hGhat : HasDecidableWordProblem Ghat) :
    ∃ (K : Type u) (_ : MonoidWithZero K) (_ : DecidableEq K) (_ : Nontrivial K),
      IsFinitelyPresentedMonoid K ∧
    ∃ (H : Type u) (_ : MonoidWithZero H) (_ : Nontrivial H) (_ : Monoid.FG H),
      HasDecidableWordProblemMonoid H ∧
      -- (i) an injective group homomorphism Ĝ → H×
      (∃ ι : Ghat →* Hˣ, Function.Injective ι) ∧
      -- (ii) an injective unital monoid homomorphism κ : T → H with κ(0_T) = ζ
      (∃ κ : TElem K →* H, Function.Injective κ ∧ κ TElem.zero = 0) ∧
      -- (iii) the finite-tuple selector property
      (∀ (d : ℕ) (h : Fin (d + 1) → H), Function.Injective h → (∀ i, h i ≠ 0) →
        ∃ L R : H, L * h 0 * R = 1 ∧ ∀ i : Fin (d + 1), i ≠ 0 → L * h i * R = 0) ∧
      -- (iv) an injective multiplicative (not necessarily unital) map c : H → K avoiding {1, Ω}
      (∃ c : H → K, (∀ x y, c (x * y) = c x * c y) ∧ Function.Injective c ∧
        ∀ h, c h ≠ 1 ∧ c h ≠ 0) ∧
      -- (v) a separator z ∈ H making (τ, τ') ↦ κ(τ) z κ(τ') injective into H \ {ζ}
      (∃ (κ : TElem K →* H) (z : H),
        (∀ τ τ' : TElem K, τ ≠ TElem.zero → τ' ≠ TElem.zero → κ τ * z * κ τ' ≠ 0) ∧
        ∀ τ1 τ1' τ2 τ2' : TElem K, τ1 ≠ TElem.zero → τ1' ≠ TElem.zero →
          τ2 ≠ TElem.zero → τ2' ≠ TElem.zero →
          κ τ1 * z * κ τ1' = κ τ2 * z * κ τ2' → τ1 = τ2 ∧ τ1' = τ2') := by
  sorry
