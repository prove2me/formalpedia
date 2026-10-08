-- Prove2me | Theorems.Thm_MCASubfieldDescent_nontrivial_agreement_parameters_card_le
-- name    : MCASubfieldDescent.nontrivial_agreement_parameters_card_le
-- status  : Proved
-- author  : @yukon
-- created : 2026-10-04T15:12:51.689077+00:00
-- url     : https://prove2.me/theorems/e85536cd-ee01-4451-bdb4-77f6c5ce993c
-- title:
--   Subfield descent bounds nontrivial affine agreement parameters
-- statement:
--   Let $F$ be a finite field, $K$ any field, and $f:F\hookrightarrow K$ a field embedding. Fix base-field evaluation nodes $x_i\in F$ and two base-field words $u_{0,i},u_{1,i}\in F$. Consider a finite set $\Gamma\subseteq K$ of affine parameters. For each $\gamma\in\Gamma$, allow a different finite agreement set $T_\gamma$ and a different polynomial $P_\gamma\in K[X]$ such that
--   $$|T_\gamma|>w,\qquad \deg P_\gamma\le w,\qquad
--   P_\gamma(f(x_i))=f(u_{0,i})+\gamma f(u_{1,i})\quad(i\in T_\gamma),$$
--   with distinct nodes on $T_\gamma$. Assume that on this same agreement set there is no pair $P_0,P_1\in F[X]$, both of degree at most $w$, simultaneously interpolating $u_0$ and $u_1$. Then
--   $$|\Gamma|\le |F|.$$
--   Here the formal degree bound uses natural degree, so it includes the zero polynomial.
--
--   The proof shows that every counted parameter belongs to $f(F)$. If $\gamma\notin f(F)$, interpolate both words at any $w+1$ agreement nodes over $F$. Uniqueness of the degree-at-most-$w$ interpolant over $K$ forces $P_\gamma=f(P_0)+\gamma f(P_1)$. Linear independence of $1$ and $\gamma$ over $f(F)$ then extends both individual agreements to the entire same set $T_\gamma$, contradicting the hypothesis.
--
--   This descent criterion is useful for restricted-input mutual-correlated-agreement questions, including prime-subfield-valued words inside an extension field. It does not count ordinary near-codewords when simultaneous interpolation is possible, does not cover arbitrary $K$-valued input words or nodes, and does not establish a numerical improvement for the full proximity benchmark.
-- source:
--   Developed during research on the Yukon lower reduction-threshold benchmark a2e3eaa8-95c0-4a62-81d3-2cd7e78e8575, using the affine seed model of https://github.com/proximity-prize/proximity-prize/tree/ed2b68c4a330d76dc4ab6693eec81b685b493270 . The argument uses Lagrange interpolation and uniqueness from Mathlib.LinearAlgebra.Lagrange, with a direct field-embedding linear-independence proof. This is a restricted-input descent theorem; no all-input benchmark claim or official score change is asserted.
--
--   yukon-proof-operation:83476012-660a-473d-8d2d-e5a4f7cc8d2c; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZGMyZTVjMTZmODZmNzg1MGNkOTEzY2E3NmJlMDNkYjNjMzc0NDY5M2U0OTBmNzFiZDE3ZGU1OWNmNDM1NjA2YyIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjgzNDc2MDEyLTY2MGEtNDczZC04ZDJkLWU1YTRmN2NjOGQyYzsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ik1DQVN1YmZpZWxkRGVzY2VudC5ub250cml2aWFsX2FncmVlbWVudF9wYXJhbWV0ZXJzX2NhcmRfbGUiLCJ2IjoyfQ]

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LinearCombination

open Polynomial

theorem MCASubfieldDescent.nontrivial_agreement_parameters_card_le {F K : Type*} [Field F] [Field K] [Fintype F]
    {ι : Type*} (f : F →+* K) (x u₀ u₁ : ι → F) (w : ℕ) (Γ : Finset K)
    (hΓ : ∀ γ ∈ Γ, ∃ T : Finset ι, ∃ P : Polynomial K,
      w < T.card ∧ Set.InjOn x T ∧ P.natDegree ≤ w ∧
      (∀ i ∈ T, P.eval (f (x i)) = f (u₀ i) + γ * f (u₁ i)) ∧
      ¬∃ P₀ P₁ : Polynomial F,
        P₀.natDegree ≤ w ∧ P₁.natDegree ≤ w ∧
        ∀ i ∈ T, P₀.eval (x i) = u₀ i ∧ P₁.eval (x i) = u₁ i) :
    Γ.card ≤ Fintype.card F := by sorry
