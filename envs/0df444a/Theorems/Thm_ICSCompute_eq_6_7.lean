-- Prove2me | Theorems.Thm_ICSCompute_eq_6_7
-- name    : ICSCompute.eq_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:48:11.562652+00:00
-- url     : https://prove2.me/theorems/938dc879-54e3-4d49-98b5-b7903ca31f74
-- title:
--   Eq. (6.7) — $Q$-blocks of $T_{\mathbf V}$ and of $T_{\mathbf V}T_{\mathbf V}^\dagger$
-- statement:
--   With the notation of (6.6) and $(M)_{x,y} := (\langle x|_Q\otimes I_E)M(|y\rangle_Q\otimes I_E)$:
--
--   1. for all $x,y$,
--   $$(T_{\mathbf V})_{x,y} = \sum_{r}\langle x|r\rangle\bigotimes_{i=1}^n B^{r_i,y_i}_{i,h_i(r)} = \bigotimes_{i=1}^n B^{x_i,y_i}_{i,h_i(x)};$$
--   2. for all $x,x'$,
--   $$\big(T_{\mathbf V}T_{\mathbf V}^\dagger\big)_{x,x'} = \sum_y (T_{\mathbf V})_{x,y}\big((T_{\mathbf V})_{x',y}\big)^\dagger = \sum_y\bigotimes_{i}\Big[B^{x_i,y_i}_{i,h_i(x)}\big(B^{x'_i,y_i}_{i,h_i(x')}\big)^\dagger\Big] = \bigotimes_{i}\Big[\sum_{v\in\{0,1\}}B^{x_i,v}_{i,h_i(x)}\big(B^{x'_i,v}_{i,h_i(x')}\big)^\dagger\Big]. \tag{6.7}$$
--
--   The last form reduces unitarity of $T_{\mathbf V}$ to a statement about each laboratory separately.
--
--   Differences from the source:
--   - generalization: unitary V_i on qubit auxiliary registers E_i, unitary U_{i,a}, h with (6.2) → arbitrary operators V_i, U_{i,a}, arbitrary finite index types E_i, any h; reason: the identities are algebraic and use none of these hypotheses; the paper's setting is a special case
--   - generalization: n ∈ ℕ (positive integers; the paper writes ℕ ∪ {0} when 0 is allowed, p.19) → n : ℕ, including n = 0; reason: the n = 0 instance is true (a single vertex, trivial registers); every positive n is an instance
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), proof of Theorem 6.1, block formula and eq. (6.7), p.34 (PDF p.36)

import Mathlib
import Definitions.Def_ICSCompute_Tmat

namespace ICSCompute

open QAlgorithms

/-- **The block formula for `(T_V)_{x,y}` and eq. (6.7)** (Shmueli, *What Can Be Computed with
Indefinite Causal Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606,
proof of Theorem 6.1, p.34 (PDF p.36)).

With `(M)_{x,y} := (⟨x|_Q ⊗ I_E) M (|y⟩_Q ⊗ I_E)`:
1. `(T_V)_{x,y} = ∑_r ⟨x|r⟩ ⨂ᵢ B^{rᵢ,yᵢ}_{i,hᵢ(r)} = ⨂ᵢ B^{xᵢ,yᵢ}_{i,hᵢ(x)}`;
2. `(T_V T_V†)_{x,x′} = ∑_y (T_V)_{x,y} ((T_V)_{x′,y})†
   = ∑_y ⨂ᵢ [B^{xᵢ,yᵢ}_{i,hᵢ(x)} (B^{x′ᵢ,yᵢ}_{i,hᵢ(x′)})†]
   = ⨂ᵢ [∑_{v ∈ {0,1}} B^{xᵢ,v}_{i,hᵢ(x)} (B^{x′ᵢ,v}_{i,hᵢ(x′)})†]` (6.7).

**Formalization Note** Arbitrary finite auxiliary index types `Eᵢ`, arbitrary operators `Vᵢ`,
`U_{i,a}` and any `h`: the identities need no unitarity and no (6.2). `⟨x|r⟩` is
`if x = r then 1 else 0`. -/
theorem eq_6_7 {n : ℕ} {E : Fin n → Type*} [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (V : (i : Fin n) → Matrix (Bool × E i) (Bool × E i) ℂ)
    (U : Fin n → Bool → Matrix Bool Bool ℂ) (h : Qubits n → Qubits n) :
    (∀ x y : Qubits n,
        qBlock (TV V U h) x y = ∑ r : Qubits n, (if x = r then (1 : ℂ) else 0) • Bprod V U h r y ∧
          ∑ r : Qubits n, (if x = r then (1 : ℂ) else 0) • Bprod V U h r y = Bprod V U h x y) ∧
      ∀ x x' : Qubits n,
        qBlock (TV V U h * (TV V U h).conjTranspose) x x' =
            ∑ y : Qubits n, qBlock (TV V U h) x y * (qBlock (TV V U h) x' y).conjTranspose ∧
          ∑ y : Qubits n, qBlock (TV V U h) x y * (qBlock (TV V U h) x' y).conjTranspose =
            ∑ y : Qubits n, piTensor (fun i => Bsub (Bblk V U i (h x i)) (x i) (y i) *
              (Bsub (Bblk V U i (h x' i)) (x' i) (y i)).conjTranspose) ∧
          ∑ y : Qubits n, piTensor (fun i => Bsub (Bblk V U i (h x i)) (x i) (y i) *
              (Bsub (Bblk V U i (h x' i)) (x' i) (y i)).conjTranspose) =
            piTensor (fun i => ∑ v : Bool, Bsub (Bblk V U i (h x i)) (x i) v *
              (Bsub (Bblk V U i (h x' i)) (x' i) v).conjTranspose) := by sorry

end ICSCompute
