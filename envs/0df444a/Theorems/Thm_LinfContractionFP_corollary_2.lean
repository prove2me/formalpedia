-- Prove2me | Theorems.Thm_LinfContractionFP_corollary_2
-- name    : LinfContractionFP.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:20:48.2018+00:00
-- url     : https://prove2.me/theorems/5058627c-11a0-4437-86d1-8fe14e8d6c65
-- title:
--   Corollary 2 and Algorithm 4 — the amplification game and Label
-- statement:
--   1. For any Oracle of accuracy $\rho>0$ for a secret $\sigma\in\mathbb R^n$ and any $\kappa>0$, $\mathrm{Amplify}(0,2\kappa,0,n,n)$ returns either a defeat of Oracle or a $\kappa$-accurate labeling of $\sigma$.
--   2. Let $0<\gamma\le1$, $f$ a $(1-\gamma)$-contraction of $[0,1]^d$ with fixed point $x^*$, $[L,U]$ a possibly degenerate box and $\tau,\varepsilon>0$. With $n=2d$ and Oracle given by ThinLabel at $\eta=\gamma\varepsilon$ (so $\rho=\gamma^2\varepsilon/8$), $\mathrm{Label}(L,U;\tau,\varepsilon)=\mathrm{Amplify}(0,2\tau,0,n,n)$ returns either an $\varepsilon$-near fixed point of $f$ or a $\tau$-accurate labeling of $[L,U]$, provided ThinLabel's recursive solves return $\gamma\eta/2$-near fixed points.
--
--   Part 2 is the specification of Label used by Solve.
--
--   Differences from the source:
--   - reading: an adversarial Oracle → any adaptive Oracle (answers may depend on the call index) meeting Problem 1's validity condition; reason: against the deterministic Amplify a history-dependent Oracle is determined by the index of the call, so this covers every adaptive and every stateless Oracle
--   - generalization: the recursive calls of Solve inside ThinLabel → any procedure solveSub meeting SubSolverSpec (η'-near fixed points of (1−γ)-contractions of dimension ≤ d/2); reason: this is the paper's inductive hypothesis; Solve itself meets it, so the statement specializes to the paper's
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Corollary 2 and Algorithm 4, p.16; Problem 1 and Remark 4, p.11

import Mathlib
import Definitions.Def_LinfContractionFP_IsOracle
import Definitions.Def_LinfContractionFP_amplify
import Definitions.Def_LinfContractionFP_IsContraction
import Definitions.Def_LinfContractionFP_IsNearFixed
import Definitions.Def_LinfContractionFP_IsAccurateLabeling
import Definitions.Def_LinfContractionFP_SubSolverSpec
import Definitions.Def_LinfContractionFP_label

namespace LinfContractionFP

/-- Corollary 2 with Algorithm 4. (a) `Amplify(0, 2κ, 0, n, n)` solves the extremal
amplification game: for any Oracle of accuracy `ρ > 0` and any `κ > 0` it returns a defeat of
Oracle or a `κ`-accurate labeling of the secret `σ`. (b) With `n = 2d` and Oracle given by
ThinLabel at `η = γε` (so `ρ = γ²ε/8`), Label(L, U; τ, ε) = `Amplify(0, 2τ, 0, n, n)` returns
either an `ε`-near fixed point of `f` or a `τ`-accurate labeling of the (possibly degenerate)
box `[L, U]`.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Corollary 2 and Algorithm 4, p.16: "Corollary 2. A solution to the extremal amplification
game from Problem 1 is obtained by Amplify(0, 2κ, 0, n, n). In particular, for a (possibly
degenerate) box [L, U] in dimension d, set n = 2d and implement Oracle using ThinLabel with
η = γε, so that ρ = γη/8 = γ²ε/8. In particular, Amplify(0, 2τ, 0, n, n) with n = 2d yields
either an ε-near fixed point or a τ-accurate labeling of [L, U], giving the algorithm
Label(L, U; τ, ε) in Algorithm 4."

**Formalization Note.** (a) is stated for any finite coordinate type (`n = |κ|`) and any
adaptive Oracle (`IsOracle`: the answer may depend on the call index); a defeat is a payload `O`
returned on some call. In (b) the
game's coordinates are the faces `ι × Bool`, Oracle is ThinLabel on the shifted box of Remark 4
(`label`), and the recursive solves inside ThinLabel are any `solveSub` meeting `SubSolverSpec`
(the paper's inductive hypothesis). Labels `−1`/`+1` are `lo`/`hi`. -/
theorem corollary_2 :
    (∀ (κ α : Type) [Fintype κ] (σ : κ → ℝ) (ρ k : ℝ), 0 < ρ → 0 < k →
      ∀ O : ℕ → (κ → ℝ) → α ⊕ (κ → Lbl), IsOracle σ ρ O →
        (∀ a, (amplifyRun O ρ 0 (2 * k) 0 (Fintype.card κ) (Fintype.card κ)).1 = Sum.inl a →
            ∃ t b, O t b = Sum.inl a) ∧
          (∀ ℓ, (amplifyRun O ρ 0 (2 * k) 0 (Fintype.card κ) (Fintype.card κ)).1 = Sum.inr ℓ →
            IsAccurate k σ ℓ)) ∧
      (∀ (ι : Type) [Fintype ι] (γ : ℝ), 0 < γ → γ ≤ 1 →
        ∀ f : (ι → ℝ) → (ι → ℝ), IsContraction γ f →
          ∀ xs ∈ unitCube ι, f xs = xs →
            ∀ solveSub : (S : Finset ι) → ((↥S → ℝ) → (↥S → ℝ)) → ℝ → (↥S → ℝ),
              SubSolverSpec γ solveSub →
                ∀ (L U : ι → ℝ) (τ ε : ℝ), 0 < τ → 0 < ε →
                  (∀ x, label γ f solveSub L U τ ε = Sum.inl x → IsNearFixed f ε x) ∧
                    (∀ ℓ, label γ f solveSub L U τ ε = Sum.inr ℓ →
                      IsAccurateLabeling τ L U xs ℓ)) := by sorry

end LinfContractionFP
