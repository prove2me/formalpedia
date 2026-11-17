-- Prove2me | Theorems.Thm_KAQROM_Supplement_theorem_7_2
-- name    : KAQROM.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:56:40.705841+00:00
-- url     : https://prove2.me/theorems/55524f6a-3480-46ea-8b9e-d013d5eb4d4b
-- title:
--   Theorem 7.2 — attack on QPKE with classical-query encryption: a classical attacker with advantage $\ge2\alpha_\Sigma-\tfrac32-\xi$
-- statement:
--   Let $\Sigma$ be a QPKE scheme with classical keys, classical-query encryption and classical ciphertexts (Definition 3.13). Key generation and decryption make at most $q_{\mathrm{Gen}}$ and $q_{\mathrm{Dec}}$ quantum queries, encryption at most $q_{\mathrm{Enc}}$ classical queries, and $Q_{\mathrm{Dec}}=\max\{1,q_{\mathrm{Dec}}\}$.
--
--   1. There is an absolute constant $C>0$ such that for every such scheme and every $0<\xi<1$ there is a computationally unbounded classical IND-CPA attacker $D_\xi$ making at most
--   $$
--   C\Bigl(\frac{q_{\mathrm{Gen}}(q_{\mathrm{Enc}}+1)^2Q_{\mathrm{Dec}}^4}{\xi^9}+\frac{q_{\mathrm{Enc}}Q_{\mathrm{Dec}}^2}{\xi^3}+1\Bigr)
--   $$
--   classical random-oracle queries with $\mathrm{Adv}^{\mathrm{IND\text{-}CPA}}_{\Sigma,D_\xi}\ge2\alpha_\Sigma-\frac32-\xi$.
--   2. If the correctness error $\epsilon_c$ is negligible and the honest query bounds are polynomial (for a family of schemes with polynomially bounded message length), then for every polynomial $p$ a classical attacker family making polynomially many queries has advantage at least $1/2-1/p(\lambda)-2\epsilon_c(\lambda)$. In particular the scheme is not query-bounded IND-CPA secure.
--
--   Together with Theorem 7.1, this restricts QPKE in the QROM whenever one of key generation or encryption has classical oracle access.
--
--   Differences from the source:
--   - encoding: security parameter λ and inputs 1^λ → one fixed λ; 1^λ arguments dropped; reason: the quantitative statement is per λ
--   - generalization: X = {0,1}^{n(λ)}, Y = {0,1}^{ℓ(λ)} with n, ℓ polynomially bounded → X any finite type, Y = Fin ℓ → ZMod 2 for any ℓ (XOR is +); reason: no bound depends on n or ℓ; the statement specializes to X = {0,1}^n
--   - encoding: quantum oracle algorithm with at most q queries → exactly q query rounds interleaved with arbitrary channels (published KAQROM.QAlg); reason: a query on the response state |+⟩^ℓ acts as the identity, so idle queries pad; parties are computationally unbounded
--   - encoding: classical oracle access → query steps whose instruments are selected by the classical record (CStage / published KAQROM.PrefixParty); reason: queries and answers are classical, the residual state stays quantum; this is Definition 3.1's notion
--   - encoding: all-zero private registers, local state preparation and private randomness inside the algorithms → arbitrary oracle-independent initial density operators; reason: local preparation from the all-zero state gives exactly these
--   - encoding: poly(λ), negl(λ), 'for every polynomial p' → λ-indexed families; the published PolyBounded and Negligible; p : Polynomial ℕ with positive values; reason: standard asymptotic notions; a positive polynomial is bounded by some (λ+2)^c
--   - reading: O(q_Gen(q_Enc+1)²Q_Dec⁴/ξ⁹ + q_Enc Q_Dec²/ξ³ + 1) → one absolute constant C > 0, quantified before every scheme, oracle space and parameter, times the printed expression; reason: the proof supplies explicit constants through Corollary 6.9
--   - encoding: a classical attacker → CINDAttacker: finitely many coin values, deterministic classical-query stages; reason: finitely many coins make the existence claim stronger
--   - generalization: 'the scheme is not query-bounded IND-CPA secure' (against quantum attackers) → not secure against classical attacker families with polynomially bounded queries; reason: classical attackers are quantum attackers, so this implies the printed claim
--   - generalization: worst-case query bound over every branch → bound required only on branches of positive probability; reason: zero-probability branches change no probability; the paper's bound implies the hypothesis
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 7.2, p.73; Definitions 3.13–3.14, p.23

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Negligible
import Definitions.Def_KAQROM_Supplement_CINDAttacker
import Definitions.Def_KAQROM_Supplement_QPKE2

namespace KAQROM.Supplement

open KAQROM
open PPADSIS.SubexpSIS

/-- **Theorem 7.2 (Attack on QPKE with classical-query encryption).** Let `Σ` be a QPKE scheme with
classical keys, classical-query encryption and classical ciphertexts, as in Definition 3.13. For
every `0 < ξ < 1` there is a computationally unbounded classical IND-CPA attacker `D_ξ` making
`O(q_Gen(q_Enc + 1)²Q_Dec⁴/ξ⁹ + q_Enc Q_Dec²/ξ³ + 1)` classical random-oracle queries,
`Q_Dec := max{1, q_Dec}`, with `Adv^{IND-CPA}_{Σ,D_ξ} ≥ 2α_Σ − 3/2 − ξ`. In particular, if the
correctness error `ϵ_c` is negligible and the honest query bounds are polynomial, the scheme is
not query-bounded IND-CPA secure: for every polynomial `p`, a classical attacker making
polynomially many queries has advantage at least `1/2 − 1/p(λ) − 2ϵ_c(λ)`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 7.2, p.73.

**Formalization Note.** The `O(·)` is one absolute constant `C > 0`, quantified before every
scheme, oracle space and parameter (the proof supplies it through Corollary 6.9). The "in
particular" part is stated for families indexed by `λ`: honest query bounds `PolyBounded`,
`ϵ_c` `Negligible` (both published), every positive-valued `p : Polynomial ℕ`; "not query-bounded
IND-CPA secure" is stated against classical attackers, which implies insecurity against the larger
class of quantum attackers. `q_Enc` is any worst-case bound on `Enc`'s classical queries. -/
theorem theorem_7_2 :
    (∃ C : ℝ, 0 < C ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] {ℓ μ : ℕ} (S : QPKE2 X ℓ μ) (qEnc : ℕ),
        S.EncQueriesLe qEnc → ∀ ξ : ℝ, 0 < ξ → ξ < 1 →
          ∃ (D : CINDAttacker S.PK S.Ct X ℓ μ) (N : ℕ), D.QueriesLe N ∧
            (N : ℝ) ≤ C * ((S.qGen : ℝ) * ((qEnc : ℝ) + 1) ^ 2 * ((max 1 S.qDec : ℕ) : ℝ) ^ 4 /
                ξ ^ 9 + (qEnc : ℝ) * ((max 1 S.qDec : ℕ) : ℝ) ^ 2 / ξ ^ 3 + 1) ∧
            2 * S.alpha - 3 / 2 - ξ ≤ S.advC D) ∧
    (∀ (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] (ℓ μ : ℕ → ℕ)
      (S : ∀ n, QPKE2 (X n) (ℓ n) (μ n)) (qEnc : ℕ → ℕ) (ϵc : ℕ → ℝ),
      (∀ n, (S n).EncQueriesLe (qEnc n)) → PolyBounded (fun n => (S n).qGen) →
      PolyBounded qEnc → PolyBounded (fun n => (S n).qDec) → PolyBounded μ →
      Negligible ϵc → (∀ n, 1 - ϵc n ≤ (S n).alpha) →
      (∀ p : Polynomial ℕ, (∀ n : ℕ, 0 < p.eval n) →
        ∃ (D : ∀ n, CINDAttacker (S n).PK (S n).Ct (X n) (ℓ n) (μ n)) (N : ℕ → ℕ),
          (∀ n, (D n).QueriesLe (N n)) ∧ PolyBounded N ∧
          ∀ n : ℕ, 1 / 2 - 1 / ((p.eval n : ℕ) : ℝ) - 2 * ϵc n ≤ (S n).advC (D n)) ∧
      ¬ (∀ (D : ∀ n, CINDAttacker (S n).PK (S n).Ct (X n) (ℓ n) (μ n)) (N : ℕ → ℕ),
          (∀ n, (D n).QueriesLe (N n)) → PolyBounded N →
          Negligible (fun n => (S n).advC (D n)))) := by sorry

end KAQROM.Supplement
