-- Prove2me | Theorems.Thm_NuclearTensor_Membership_lemma_4_3
-- name    : NuclearTensor.Membership.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:18:31.804379+00:00
-- url     : https://prove2.me/theorems/f518f131-dd9e-4f02-bb3f-81ee5a3c0824
-- title:
--   Lemma 4.3 — optimization meta-algorithm (corrected: nonempty local sets)
-- statement:
--   Let each local set $K_j\subseteq B_{H_j}$ be compact and nonempty, let $\|M\|_F\le1$, and let $\epsilon>0$. Supply finite code that constructs a reachable-message cover with witnesses in time $T_{\rm cover}$ and finite code that returns both the maximum terminal value and an actual feasible maximizing point for every final message in time $T_{\rm term}$. Algorithm 2 returns an actual feasible tuple with
--   $$\langle M,x_1\otimes\cdots\otimes x_m\rangle\ge\max_{y_j\in K_j}\langle M,y_1\otimes\cdots\otimes y_m\rangle-m\delta-2\eta\sqrt m.$$
--   With $\epsilon_0=\min(\epsilon,1)$, $\eta=\epsilon_0/(8\sqrt m)$, and $\delta=\epsilon_0/(4m)$, the error is at most $\epsilon_0/2\le\epsilon/2$, retaining the stated $O(\epsilon)$ claim. Its actual runtime is bounded by a uniform constant times
--   $$\operatorname{poly}(|M|,m)+T_{\rm cover}+|S_{m-1}|T_{\rm term}.$$
--   The cover in the conclusion is tied to an actual execution of the supplied cover routine; terminal selection and stored-witness traceback are explicit. This target supplies both correctness and execution complexity of the modular algorithm.
--
--   Differences from the source:
--
--   - encoding: finite-dimensional real Hilbert spaces, indexed from 1 → zero-based row-major Euclidean coordinates, allowing zero-dimensional local spaces; reason: orthonormal coordinates represent every source finite real Hilbert space; positive tensor order is the source convention
--   - reading: polynomial time on arbitrary real inputs with polynomial-time SVD and stipulated local linear optimizers → finite offline real-RAM programs with scalar arithmetic, square root, charged full SVD, explicit finite-code calls, and only the stipulated local services; reason: the source specifies no bit lengths; fixed positive model parameters A and q charge spectral and local operations, while actual executions determine every total runtime
--   - correction: Lemma 4.3 states compact local sets but does not require nonemptiness → every local set is additionally nonempty; reason: for m=2, M=0, K1=empty and K2={0}, all printed subroutine hypotheses hold: S0={1}, S1=empty is a cover and the terminal routine returns 0; a feasible output tuple is impossible
--   - encoding: Theta(epsilon/sqrt(m)) compression, Theta(epsilon/m) covers, and O(epsilon) meta-algorithm error → epsilon0=min(epsilon,1), eta=epsilon0/(8 sqrt(m)), delta=epsilon0/(4m), exact error m delta+2 eta sqrt(m); reason: the p.17 proof gives this exact error, equal to epsilon0/2, for these legitimate source-order parameters
--   - encoding: poly(|M|,m)+Tcover+|Slast|Tterm asymptotic runtime → B times (inputSize^p+Tcover+|Slast|Tterm), with positive B,p fixed before instances; reason: makes the uniform hidden polynomial and constant overhead explicit while charging all calls and output copies
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), pp.16–17, Lemma 4.3 and its proof

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

/-- Corrected by requiring nonempty local sets. For m=2, M=0, K₁=∅ and K₂={0},
the printed compactness, cover and terminal-oracle hypotheses all hold, but no feasible
output tuple exists. The cover has S₀={1}, S₁=∅, and the terminal routine returns 0. -/
theorem lemma_4_3 :
    ∃ P : Program, ∀ (σ : Spectral) (ω : Option LocalOracle) (A q : ℕ), 0 < A → 0 < q →
      ∃ B p : ℕ, 0 < B ∧ 0 < p ∧
      ∀ (ds : List ℕ), ds ≠ [] →
      ∀ (K : (j : ℕ) → Set (Vec (ds.getD j 0))),
      (∀ j < ds.length, IsCompact (K j) ∧ (K j).Nonempty ∧ K j ⊆ unitBall (ds.getD j 0)) →
      ∀ (M : Tensor ds), ‖M‖ ≤ 1 → ∀ ε : ℝ, 0 < ε →
      let η := compressionAccuracy ε ds.length
      let δ := coverAccuracy ε ds.length
      ∀ C : PrefixData ds, algorithm1 σ η M C →
      ∀ (Pcover Pterm : Program) (Tcover Tterm : ℝ),
        coverContract σ ω A q η δ M C K Pcover Tcover →
        terminalContract σ ω A q C K Pterm Tterm →
        ∃ (S : FiniteCover C) (sc : Configuration) (cc : ℕ),
          Executes σ ω A q [] Pcover
            (initConfig (coverInputIntegers C) (coverInputReals η δ M C)) sc cc ∧
          outputsCover sc S ∧ finiteCoverProperty C K δ S ∧
          runsWithin σ ω A q [Pcover, Pterm] P (ds.map Int.ofNat) ([ε] ++ encodeVec M)
            (B * ((inputSize ds : ℝ) ^ p + Tcover + S.count (ds.length - 1) * Tterm))
            (fun s => ∃ x : Tuple ds,
              outputsTuple s x ∧ algorithm2Output C K S x ∧ x ∈ feasible K ∧
              inner ℝ M (product x) ≥ optimum M K -
                (ds.length * δ + 2 * η * Real.sqrt ds.length)) := by sorry

end NuclearTensor.Membership
