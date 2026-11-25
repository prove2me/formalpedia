-- Prove2me | Theorems.Thm_IntConeFPT_counted_threshold_driver
-- name    : IntConeFPT.counted_threshold_driver
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-25T15:01:58.30451+00:00
-- url     : https://prove2.me/theorems/65da893b-d04a-5103-82b8-e8af9feb5419
-- title:
--   §3.5 — Turing-machine orchestration for candidate-enumerated threshold search
-- statement:
--   Let $I$ be a valid instance, $N_{\max} \in \mathbb Z_{\ge 0}$, $x$ the encoded input $(I, N_{\max})$ of length $L$, $q$ the common denominator of the cost polynomial coefficients, $B = 2^{L^2 + 4L}$, and $k \le 2B$ a scaled objective index corresponding to rational budget $\gamma = (k - B)/q$.
--
--   Given two deterministic multi-stack Turing machines $M_{13}$ (solving Lemma 13 integer feasibility and lifting on canonical candidate tuples) and $M_6$ (solving Lemma 6 constructive residue decomposition on individual blocks), there exist a constant $C_{\mathrm{drv}}$ and a deterministic driver machine $W$ that orchestrates one budget test on input $(x, k)$ as follows:
--
--   1. Compute $\gamma = (k - B)/q$ and enumerate all canonical candidate residue tuples $R = (R^{(1)}, \dots, R^{(\tau)})$ with $|R^{(t)}| \le 2^d$ and each $R^{(t)}$ strictly sorted by its coordinate key.
--   2. For each canonical candidate $R$, invoke $M_{13}$ on $(x, R, \gamma)$ (taking at most $T_{13}$ steps). If every canonical candidate returns `none`, $W$ outputs `infeasible`.
--   3. Otherwise, for the first canonical candidate $R$ returning `some s`, invoke $M_6$ on each block $(I, t, R^{(t)}_i, z^{(t)}_i, w^{(t)}_i, n^{(t)}_i)$ (taking at most $T_6$ steps), merge duplicate generators per type while summing their positive multiplicities, compute the rational total aggregate $(y, v)$, and output `optimal y v cert`.
--
--   The total running time of $W$ is bounded by $(N_{\mathrm{cand}} + L + 2^d + T_{13} + T_6 + 2)^{C_{\mathrm{drv}}}$, where $N_{\mathrm{cand}}$ is the number of candidate tuples from Corollary 8.
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328, §3.5, proof of Proposition 14, pp. 16–17

import Definitions.Def_IntConeFPT_Homogenized
import Definitions.Def_IntConeFPT_Machine

open OnlineCRS.Combine IntConeFPT

theorem IntConeFPT.counted_threshold_driver (M_13 M_6 : Machine) :
    ∃ C_drv : ℕ, ∃ W : Machine,
      ∀ (I : Instance), I.Valid → ∀ (N : ℕ),
        let x := encInstance I ++ encNat N ++ [3]
        let B := 2 ^ (x.length ^ 2 + 4 * x.length)
        let q := ∏ t, ∏ j, (I.coeff t j).den
        ∀ (k : ℕ), k ≤ 2 * B →
          let γ : ℚ := ((k : ℤ) - (B : ℤ)) / (q : ℚ)
          let Canon : Cand I → Prop := fun R =>
            ∀ t, (R t).length ≤ 2 ^ I.d ∧
              ((R t).map fun r => (List.finRange I.d).map fun j => (r j : ℕ)).Pairwise (· < ·)
          let N_cand : ℕ :=
            ((Finset.univ : Finset (Fin I.τ → Finset (Residue I.d))).filter
              (fun R => ∀ t, (R t).card ≤ 2 ^ I.d)).card
          ∀ (o : (R : Cand I) →
              Option ((t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ))
            (out : (R : Cand I) →
              ((t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ) →
              (t : Fin I.τ) → Fin (R t).length →
              List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ))
            (T_13 T_6 : ℝ),
            0 ≤ T_13 → 0 ≤ T_6 →
            (∀ R, Canon R →
              RunsWithin M_13 (x ++ encCand R ++ encRat γ ++ [3]) (encLift (R := R) (o R)) T_13) →
            (∀ R, Canon R → ∀ s, o R = some s → ∀ t i,
              (∀ e ∈ out R s t i, 1 ≤ e.2.2) ∧
              RunsWithin M_6
                (encLocal I t ((R t).get i) ++ encIntVec (s t i).1 ++ encVec (s t i).2.1 ++
                  encNat (s t i).2.2 ++ [3])
                (encCert (out R s t i)) T_6) →
            ((∀ R, Canon R → o R = none) ∧
              RunsWithin W (x ++ encNat k ++ [3]) (encOutput (I := I) .infeasible)
                (((N_cand : ℝ) + (x.length : ℝ) + (2 ^ I.d : ℝ) + T_13 + T_6 + 2) ^ C_drv)) ∨
            (∃ (R : Cand I)
               (s : (t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ)
               (cert : Cert I),
              Canon R ∧ o R = some s ∧
              (∀ t, (cert t).length ≤ ∑ i : Fin (R t).length, (out R s t i).length ∧
                ((cert t).map fun c => (c.1, c.2.1)).Nodup ∧
                (∀ c ∈ cert t, 1 ≤ c.2.2 ∧ ∃ i, ∃ e ∈ out R s t i, (e.1, e.2.1) = (c.1, c.2.1)) ∧
                certMult I cert t =
                  ∑ i : Fin (R t).length,
                    ((out R s t i).map fun e => Finsupp.single (certGen e) e.2.2).sum) ∧
              let y : Fin I.d → ℚ :=
                fun j => ∑ t : Fin I.τ, ∑ i : Fin (R t).length, ((s t i).1 j : ℚ)
              let v : Fin I.k → ℚ :=
                fun j => ∑ t : Fin I.τ, ∑ i : Fin (R t).length, (s t i).2.1 j
              RunsWithin W (x ++ encNat k ++ [3]) (encOutput (.optimal y v cert))
                (((N_cand : ℝ) + (x.length : ℝ) + (2 ^ I.d : ℝ) + T_13 + T_6 + 2) ^ C_drv)) := by sorry
