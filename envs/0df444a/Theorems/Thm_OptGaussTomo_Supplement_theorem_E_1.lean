-- Prove2me | Theorems.Thm_OptGaussTomo_Supplement_theorem_E_1
-- name    : OptGaussTomo.Supplement.theorem_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:46:40.41221+00:00
-- url     : https://prove2.me/theorems/fbc3d044-d6e2-4df5-a49f-c585cba04653
-- title:
--   Theorem E.1 — random purification channel for infinite direct sums $\bigoplus_\lambda\mathcal L_\lambda\otimes\mathcal R_\lambda$
-- statement:
--   Let $\Lambda$ be a countable index set and $\mathcal H\cong\bigoplus_{\lambda\in\Lambda}\mathcal L_\lambda\otimes\mathcal R_\lambda$ with every $\mathcal L_\lambda,\mathcal R_\lambda$ finite dimensional (E.1), with the von Neumann algebras $\mathcal A\cong\bigoplus_\lambda I_{\mathcal L_\lambda}\otimes L(\mathcal R_\lambda)$ and $\mathcal B\cong\bigoplus_\lambda L(\mathcal L_\lambda)\otimes I_{\mathcal R_\lambda}$ (E.2), the projections $P_\lambda$ onto the blocks, and the map $\mathcal E_{\mathcal A}$ of (E.3). Then there is a quantum channel $\mathcal P_{\mathcal A}:T(\mathcal H)\to T(\mathcal H\otimes\tilde{\mathcal H})$ with the following properties.
--
--   1. **Random purification of invariant input states.** For every state $\rho$ that commutes with $\mathcal A$ (i.e. $\rho\in\mathcal B$),
--   $$
--   \mathcal P_{\mathcal A}[\rho]=(\mathcal I\otimes\mathcal E_{\mathcal A})[\psi^{\mathrm{std}}_\rho]=\int_G(I\otimes g)\,\psi^{\mathrm{std}}_\rho\,(I\otimes g^\dagger)\,dg \tag{E.5}
--   $$
--   for every closed compact subgroup $G\subseteq U(\mathcal H)$ with $G''=\mathcal B$, integrated against its normalized Haar measure.
--
--   2. **Explicit formulas.** For every state $\rho$,
--   $$
--   \mathcal P_{\mathcal A}[\rho]\cong\bigoplus_{\lambda\in\Lambda}\operatorname{tr}_{\mathcal R_\lambda}[P_\lambda\rho P_\lambda]\otimes\frac{I_{\tilde{\mathcal L}_\lambda}}{\dim\mathcal L_\lambda}\otimes\frac{|\Gamma\rangle\langle\Gamma|_{\mathcal R_\lambda\tilde{\mathcal R}_\lambda}}{\dim\mathcal R_\lambda} \tag{E.6}
--   $$
--   $$
--   =\sum_k\sqrt{\mathcal P_{\mathcal A}[Q_k]}\,(\rho\otimes I)\,\sqrt{\mathcal P_{\mathcal A}[Q_k]} \tag{E.7}
--   $$
--   for every collection $(Q_k)$ of finite-rank central projections (elements of $\mathcal A\cap\mathcal B$) with $\sum_kQ_k=I$; both sums converge in trace norm.
--
--   This extends the random purification channel of the finite-dimensional Theorem B.1 to infinite direct sums with finite-dimensional blocks, the situation of passive bosonic Gaussian unitaries; Corollary E.2 and Corollary 5.3, used for bosonic Gaussian tomography, are its applications.
--
--   **Formalization Note** $\mathcal H=\ell^2$ of the triples $(\lambda,l,r)$ with $\dim\mathcal L_\lambda=a(\lambda)$, $\dim\mathcal R_\lambda=b(\lambda)$; its fixed basis, used for $\psi^{\mathrm{std}}_\rho$, is the product basis. Operators are coefficient arrays, and trace class, states and channels are the published notions of `QAlgorithms_Papers_Independent_Dependency50_P33`. The compact group enters as an abstract compact group with a Haar probability measure and a continuous unitary homomorphism into $U(\mathcal H)$, whose image is the subgroup; the integral is entrywise.
--
--   Differences from the source:
--   - reading: H a separable Hilbert space with a fixed orthonormal basis, H ≅ ⊕_λ L_λ ⊗ R_λ, and the standing simplification that A (hence B) is closed under transposes → H = ℓ²(Σ λ, Fin (a λ) × Fin (b λ)) whose fixed basis is the product basis |λ,l,r⟩ induced by (E.1); no transpose hypothesis; reason: the proof works in this basis ('With respect to the bases induced by (E.1)', (E.9)); in it A and B are closed under transposes, so the simplification holds and is not a separate hypothesis
--   - encoding: operators on H, T(H), S(H), quantum channel T(H) → T(H ⊗ H̃) → coefficient arrays on ℓ²(X); the published P33 IsTraceClass, State and IsTraceClassChannel (linear, completely positive, trace preserving on trace class); reason: same objects in coordinates
--   - encoding: any closed compact subgroup G ⊆ U(H) with its normalized Haar measure dg → any compact group G with a Haar probability measure μ and a continuous homomorphism π into unitary coefficient arrays (entrywise topology); reason: the image π(G) is a closed compact subgroup and the image of μ its normalized Haar measure; every closed compact subgroup arises (π the inclusion); on U(H) the entrywise topology is the strong (= weak) operator topology
--   - encoding: G'' = B → commutant (commutant (range π)) = {M | InAlgB M}, commutants taken among bounded operators; reason: the paper's definition of the commutant
--   - encoding: the integral ∫_G (I ⊗ g) ψ^std_ρ (I ⊗ g†) dg → entrywise integrals, each integrable, equal to the entries of P_A[ρ] (published IsBarycenter); reason: the trace-norm Bochner integral exists here and its entries are the entrywise integrals; entries determine the operator
--   - encoding: ρ ⊗ I in (E.7), √ of a positive operator → productCoeff ρ 1; opSqrt, the unique positive bounded square root; reason: same objects in coordinates
--   - encoding: finite-rank central projections Q_k with ∑_k Q_k = I; 'the sums converge in trace norm' → Q indexed by an arbitrary index type K, Q k ∈ A ∩ B, Q k† = Q k = Q k Q k, finite rank, ∑ Q k = I strongly (unconditionally); both sums converge unconditionally in trace norm (TraceHasSum); reason: central means in the centre A ∩ B (the proof: 'Q_k ∈ A ∩ B'); the collections are unordered, so sums are unconditional
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Theorem E.1, pp.63–64 (pdf pp.63–64), eqs. (E.5)–(E.7)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_OptGaussTomo_Supplement_mulOp
import Definitions.Def_OptGaussTomo_Supplement_opSqrt
import Definitions.Def_OptGaussTomo_Supplement_TraceHasSum
import Definitions.Def_OptGaussTomo_Supplement_BlockIdx
import Definitions.Def_OptGaussTomo_Supplement_condExpA
import Definitions.Def_OptGaussTomo_Supplement_stdPurif
import Definitions.Def_OptGaussTomo_Supplement_purifBlock

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClassChannel IsBarycenter productCoeff)
open MeasureTheory

namespace OptGaussTomo.Supplement

open Classical in
/-- **Theorem E.1** (Random purification for infinite direct sums; Chen, Fanizza, Girardi, Lami,
Mele, Walter, Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*,
arXiv:2607.11847, held version, sha256 0f7548a2…, Theorem E.1, pp.63–64). Let
`H ≅ ⊕_{λ∈Λ} L_λ ⊗ R_λ` with `Λ` countable and `L_λ, R_λ` finite dimensional (E.1), and `A`, `B` as
in (E.2). There is a quantum channel `P_A : T(H) → T(H ⊗ H̃)` such that
1. for every state `ρ` commuting with `A` (i.e. `ρ ∈ B`),
   `P_A[ρ] = (I ⊗ E_A)[ψ^std_ρ] = ∫_G (I ⊗ g) ψ^std_ρ (I ⊗ g†) dg` for every closed compact
   subgroup `G ⊆ U(H)` with `G″ = B` (E.5);
2. for every state `ρ`, `P_A[ρ] ≅ ⊕_λ tr_{R_λ}[P_λρP_λ] ⊗ I_{L̃_λ}/dim L_λ ⊗ |Γ⟩⟨Γ|/dim R_λ`
   (E.6) `= ∑_k √(P_A[Q_k]) (ρ ⊗ I) √(P_A[Q_k])` (E.7) for every collection of finite-rank
   central projections `Q_k` with `∑_k Q_k = I`, both sums converging in trace norm.

**Formalization Note.**
* `H = ℓ²(BlockIdx a b)` with `dim L_λ = a λ`, `dim R_λ = b λ`; its fixed basis is the product
  basis induced by (E.1), in which `A` is closed under transposes (the paper's standing
  simplification, p.63). `H̃` is the second coordinate of `ℓ²(X × X)`.
* Operators are coefficient arrays; trace class, states and channels (linear, completely positive,
  trace preserving on trace class) are the published `P33` notions.
* A closed compact subgroup `G ⊆ U(H)` with its normalized Haar measure is given as a compact
  group `G` with a Haar probability measure `μ` and a continuous unitary homomorphism `π` into the
  coefficient arrays (entrywise topology, which on `U(H)` is the strong operator topology); its
  image is the subgroup and the image of `μ` its Haar measure. `G″ = B` is the double commutant of
  `π(G)` among bounded operators. The integral is taken entrywise (`IsBarycenter`).
* "Central projection" is membership in `A ∩ B`; `∑_k Q_k = I` is strong unconditional
  convergence; "the sums converge in trace norm" is `TraceHasSum`. -/
theorem theorem_E_1 {Λ : Type} [Countable Λ] (a b : Λ → ℕ) :
    ∃ P : Matrix (BlockIdx a b) (BlockIdx a b) ℂ →
        Matrix (BlockIdx a b × BlockIdx a b) (BlockIdx a b × BlockIdx a b) ℂ,
      IsTraceClassChannel P ∧
      (∀ ρ : State (BlockIdx a b),
        (∀ M, InAlgA a b M → mulOp ρ.coefficients M = mulOp M ρ.coefficients) →
          P ρ.coefficients = applySecond (condExpA a b) (stdPurif ρ.coefficients) ∧
          ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
            [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
            [IsProbabilityMeasure μ] (π : G → Matrix (BlockIdx a b) (BlockIdx a b) ℂ),
            Continuous π → (∀ g, IsUnitaryCoeff (π g)) →
            (∀ g h, π (g * h) = mulOp (π g) (π h)) →
            commutant (commutant (Set.range π)) = {M | InAlgB a b M} →
            IsBarycenter μ (fun g => twirlTerm (π g) ρ.coefficients) (P ρ.coefficients)) ∧
      (∀ ρ : State (BlockIdx a b),
        TraceHasSum (purifBlock a b ρ.coefficients) (P ρ.coefficients) ∧
        ∀ (K : Type) (Q : K → Matrix (BlockIdx a b) (BlockIdx a b) ℂ),
          (∀ k, InAlgA a b (Q k) ∧ InAlgB a b (Q k)) → (∀ k, IsProjCoeff (Q k)) →
          (∀ k, IsFiniteRank (Q k)) → SumsToIdStrongly Q →
          TraceHasSum
            (fun k => mulOp (mulOp (opSqrt (P (Q k))) (productCoeff ρ.coefficients 1))
              (opSqrt (P (Q k))))
            (P ρ.coefficients)) := by sorry

end OptGaussTomo.Supplement
