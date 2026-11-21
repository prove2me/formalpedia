-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_ShortProbe_good_real_trial
-- name    : InfoLossLAR.WorstCase.ShortProbe.good_real_trial
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T04:42:24.610758+00:00
-- url     : https://prove2.me/theorems/48efe907-41f4-4852-8422-810743ee745f
-- title:
--   A successful fixed-family search trial with independent rounding bits
-- statement:
--   Suppose $A$ recovers every secret of the prescribed LWE family with probability at least $3/4$ on sufficiently large dimensions in $S$. Let $B$ be a nonsingular integer $n\times n$ basis, let $R>\sqrt2 q_n\eta_{\epsilon_n}(B\mathbb Z^n)$, and suppose $B^\top u=z\in\mathbb Z^n$ with $R\lVert x-u\rVert<\sigma_n/2$. Draw the coefficient rows independently from the discrete Gaussian of width $R$ and supply independent uniform bits to the numerical table constructor.
--
--   If $m$ is the total number of rows, polynomially bounded in $n$, set $M=768(m+1)$. For some $i\in\{0,\ldots,M\}$, use squared variance $v_i=\sigma_n^2-(\sigma_n^2/2)i/M$, cutoff $\sigma_n M$ and $M$ precision bits. For all sufficiently large $n\in S$, running $A$ on the resulting observed table gives
--   $$
--   \Pr[\text{decoded output}=z\bmod q_n]\geq 17/24.
--   $$
--   The probability averages the Gaussian pool, numerical tape and Born measurement.
-- source:
--   Derivation for InfoLossLAR.WorstCase.RegevSearch.search_to_dual_candidate_lists, A successful fixed-family search trial with independent rounding bits. https://prove2.me/theorems/98258395-a948-48ad-91ba-ef2767f47f76

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05
import Definitions.Def_InfoLossLAR_RegevSearch
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSearch InfoLossLAR.WorstCase.NativeLWETableLoader
open RegevLWE.GaussConv AFT Integration9_9.LARPlatformEncoding
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.ShortProbe

theorem good_real_trial (p samples : Polynomial ℕ) (hp : ∀ n, samples.eval n*famd n ≤ p.eval n)
    (A : MFamily) (cutoff : ℕ) (S : Set ℕ) (hsearch : SearchOn A samples cutoff S) :
    ∃ N : ℕ, ∀ n ∈ S, N ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det≠0 →
    ∀ (R : ℚ), 0 < R →
      Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n) < (R:ℝ) →
    ∀ (x u : Fin n → ℚ) (z : Fin n → ℤ), (∀ j,∑ i,(B i j:ℚ)*u i=z j) →
      (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2) < (famσ n:ℝ)^2/4 →
    ∃ i : Fin ((768*(samples.eval n*famd n+1)) + 1),
      let M := (768*(samples.eval n*famd n+1))
      let rows := samples.eval n*famd n
      let v := ((famσ n:ℚ)^2-((famσ n:ℚ)^2/2)*(i.val:ℚ)/M)
      let cutoff' := famσ n*M
      let bits := M
      (17/24:ℝ) ≤ ∑' vals : Fin rows → Fin n → ℤ,(∏ j, coefficientMass B (R:ℝ) (vals j)) *
        (FiniteDist.uniform (Fin (rows*((bits+1)+(2*cutoff'+1)+1)) → Fin 2)).expectation
        (fun tape => outputProb A (observed ((unary n,famPP n),((List.replicate (samples.eval n) (),List.replicate (famd n) ()),
             ((((List.ofFn (fun i => List.ofFn (B i)),List.ofFn x),
               (famq n,(v,(List.replicate cutoff' (),List.replicate bits ())))),List.ofFn (fun i => List.ofFn (vals i))),
                List.ofFn (fun j => decide ((tape j).val=1)))))) (fun raw => (readVector raw).2=List.ofFn fun j => (z j:ZMod (famq n)).val)) := by sorry

end InfoLossLAR.WorstCase.ShortProbe
