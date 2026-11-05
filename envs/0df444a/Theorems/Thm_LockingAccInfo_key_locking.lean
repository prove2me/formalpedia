-- Prove2me | Theorems.Thm_LockingAccInfo_key_locking
-- name    : LockingAccInfo.key_locking
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:10.082502+00:00
-- url     : https://prove2.me/theorems/2f520c20-3467-4521-a208-4c28ac16f924
-- title:
--   §VI (i)–(ii), Eq. (9) (corrected: $I_{\mathrm{acc}}(S;ES_1\dots S_{n-1})=H(S)$, not $n$) — a key with $I_{\mathrm{acc}}(S;E)\le e^{-(n-2)/8}$ whose last bit is revealed given the others
-- statement:
--   Let $n\ge3$ and let $m$ be the largest integer with $3^m\le2^{n-1}$. Let $\rho_{XYE}$ be the {ccq}-state of Eq. (3): $(X,Y)$ uniform on $\{0,1\}\times\{1,2,3\}^m$, $E$ an $m$-qubit system in the state $2^{-m}(\mathrm{id}+(-1)^x\sigma_y)$. Let $g:\{1,2,3\}^m\to\{0,1\}^{n-1}$ be any injective map and let $S=(S_1,\dots,S_n)=(g(Y),X)$ be the $n$-bit key. Write $I_{\mathrm{acc}}$ for accessible information, $H$ for Shannon entropy in bits, and $\Delta=I_{\mathrm{acc}}(XY;YE)-I_{\mathrm{acc}}(XY;E)$. Then:
--
--   1. $I_{\mathrm{acc}}(S;E)=I_{\mathrm{acc}}(XY;E)$;
--   2. $I_{\mathrm{acc}}(S;E)\le(2/3)^{m/2}$;
--   3. (Eq. (9))
--
--   $$
--   I_{\mathrm{acc}}(S;E)\;\le\;e^{-(n-2)/8};
--   $$
--
--   4. for every value $s'$ of the first $n-1$ bits that occurs, there is a two-outcome measurement on $E$ alone that outputs $S_n$ with certainty;
--   5. $I_{\mathrm{acc}}(S;ES_1\dots S_{n-1})=H(S)=1+m\log_23$;
--   6. $I_{\mathrm{acc}}(XY;YE)=H(XY)=1+m\log_23$;
--   7. $H(Y)=m\log_23$, $\;H(Y)+1-(2/3)^{m/2}\le\Delta\le H(Y)+1$ and $H(Y)<\Delta$; the same three bounds hold for the key's gain $I_{\mathrm{acc}}(S;ES_1\dots S_{n-1})-I_{\mathrm{acc}}(S;E)$.
--
--   So the key meets the accessible-information security criterion with an exponentially small parameter, yet an adversary who learns the first $n-1$ bits (for instance from a one-time-pad ciphertext of a known message prefix) learns the last bit exactly. Accessible information is therefore not a composable security criterion.
--
--   **Formalization Note** The paper prints the value in (ii) as $n$; that is not attained by the §IV key, whose entropy is $1+m\log_23<n$, and clause 5 states the attained value.
--
--   Differences from the source:
--   - correction: §VI (ii): Iacc(S; E S₁,…,S_{n−1}) = n → Iacc(S; (S₁…S_{n−1}) E) = H(S) = 1 + m log₂3; reason: the key of §IV takes 2·3^m < 2^n values, so Iacc ≤ H(S) = 1 + m log₂3 < n; at n = 3, m = 1: H(S) = log₂6 < 3, with every assumption of the source satisfied
--   - reading: m ≈ n/log₂3 → m = Nat.log 3 (2^(n−1)), the largest m with 3^m ≤ 2^{n−1}, for every n ≥ 3; reason: the stronger of the two readings: it covers every n, as §VI's 'for any n ∈ ℕ' requires, while the narrower one (2^{n−2} ≤ 3^m) skips n = 4, 7, 10, 12, …
--   - reading: for some bijective mapping f, ρ_{S_n f(S₁,…,S_{n−1}) E} = ρ_XYE → an arbitrary injective g : {1,2,3}^m → {0,1}^{n−1}, S = (g(Y), X), with f = g⁻¹ on the range of g; reason: no bijection {0,1}^{n−1} → {1,2,3}^m exists since 2^{n−1} ≠ 3^m (footnote 28 says S is not uniform on the key space); every injective g is covered
--   - reading: Δ is larger than the size of Y → H(Y) < Δ with H(Y) = log₂|Y| = m log₂3; reason: the size is the quantity H(Y) in the same sentence; the integer reading ⌈log₂|Y|⌉ is false at m = 2 (a measurement found numerically gives Δ ≤ 3.898 < 4)
--   - encoding: for any n ∈ ℕ → 3 ≤ n; reason: a nondegeneracy condition that only excludes undefined cases: (3) is a state only for m ≥ 1, which needs 3 ≤ 2^{n−1}
--   - encoding: Iacc(S;E) is exponentially small in n → the explicit bounds Iacc(S;E) ≤ (2/3)^{m/2} and Iacc(S;E) ≤ e^{−(n−2)/8} of Lemma 2 and Eq. (9); reason: the paper's own quantitative form of the claim (Eq. (9))
--   - encoding: given the first n − 1 bits of S, a measurement on E determines the nth bit with certainty → for every prefix s′ of positive probability a POVM {M_x}_{x∈Bool} on E with tr(M_{x′} ρ_{E|S=(s′,x)}) = [x′ = x]; reason: the same statement for the conditional states of the key
--   - encoding: Iacc = max over all local POVMs M of I(V;Z) → published accessibleInformation: sSup over finite POVMs with any number of outcomes of H(V) + H(Z) − H(VZ); reason: for a finite ensemble the optimum is attained by a finite POVM; the value set is nonempty and bounded above by H(V) (proved in the sanity file), so sSup is the maximum
--   - encoding: Iacc(V; YE): systems Y and E combined (footnote 23) → withRegister: conditional state |π(v)⟩⟨π(v)| ⊗ ρ_{E|V=v} on the index type P × Q, register first; reason: the {cq}-state ρ_{V(YE)} of footnote 23; the order of the two factors does not change the accessible information
--   - encoding: n-bit string S = (S₁,…,S_n), X = {0,1}, Y = {1,2,3}^m, entropies → pair (Fin (n−1) → Bool, Bool); Bool with false = 0; Fin m → Fin 3 shifted by Fin.succ; Shannon entropy in bits; reason: Lean convention; the same objects
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §VI (i)–(ii), p.4; §IV, Eq. (9), p.3; Lemmas 1–2, p.2; §III closing, p.3; footnotes 23, 27, 28, p.5

import Mathlib
import Definitions.Def_LockingAccInfo_lockEnsemble
import Definitions.Def_LockingAccInfo_keyEnsemble
import Definitions.Def_LockingAccInfo_withRegister
open QAlgorithms (IsPOVM IsDensityMatrix effectProb)
open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData accessibleInformation ensembleMean)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, §VI (i)–(ii), p.4: "a classical
n-bit string S = (S1, . . . , Sn) (for any n ∈ N) and a quantum system E such that the following
holds: (i) any measurement on E chosen independently of S only reveals a negligible amount of
information about S (i.e., Iacc(S; E) is exponentially small in n) and (ii) given the first n − 1
bits of S, there exists a measurement on E which determines the value of the nth bit with
certainty (i.e., Iacc(S; ES1, . . . , Sn−1) = n)"; with Eq. (9), p.3, "Iacc(S; E) = Iacc(XY; E) ≤ ε,
where ε := e^{−(n−2)/8}", Lemma 2, p.2, and §III closing, p.3: "Iacc(XY; EY) = H(XY) … the quantity
∆ = Iacc(XY; EY) − Iacc(XY; E) … is arbitrarily close to H(Y) + 1 … The difference ∆ is larger than
the size of Y."

For every `n ≥ 3`, with `m` the largest integer such that `3^m ≤ 2^{n−1}`, and every injective
encoding `g` of `Y = {1,2,3}^m` into the first `n − 1` key bits (key `S = (g(Y), X)`, §IV):
1. `Iacc(S;E) = Iacc(XY;E)` (first equality of (9));
2. `Iacc(S;E) ≤ (2/3)^{m/2}` (Lemma 2);
3. `Iacc(S;E) ≤ e^{−(n−2)/8}` (Eq. (9));
4. for every value of the first `n − 1` bits that occurs, a two-outcome POVM on E alone outputs
   the `n`th bit with certainty (§VI (ii), Lemma 1);
5. `Iacc(S; (S₁…S_{n−1})E) = H(S) = 1 + m log₂ 3` (§VI (ii), corrected: the printed value `n` is
   not attained, since `H(S) = 1 + m log₂ 3 < n`; for n = 3, H(S) = log₂ 6 < 3);
6. `Iacc(XY; YE) = H(XY) = 1 + m log₂ 3` (§III closing; the uniform key of footnote 28);
7. `H(Y) = m log₂ 3`, and `∆ = Iacc(XY;YE) − Iacc(XY;E)` satisfies
   `H(Y) + 1 − (2/3)^{m/2} ≤ ∆ ≤ H(Y) + 1` and `H(Y) < ∆`; the same for the key gain
   `Iacc(S;(S₁…S_{n−1})E) − Iacc(S;E)`.

**Formalization Note.** The key is the pair (prefix `Fin (n-1) → Bool`, last bit `Bool`) and
`keyEnsemble g` places weight `1/(2·3^m)` on `(g y, x)` with E in state (3); no bijection
`{0,1}^{n−1} → Y` exists (footnote 28), so `f` is `g⁻¹` on the range of `g`. Iacc is the published
`accessibleInformation` (supremum over finite POVMs of any size, bits). The classical prefix
(resp. Y) is appended to E with `withRegister` (footnote 23). "Size of Y" is read as
`H(Y) = log₂|Y|`. `n ≥ 3` is the range where (3) is a state (`m ≥ 1`). -/
theorem key_locking (n : ℕ) (hn : 3 ≤ n)
    (g : (Fin (Nat.log 3 (2 ^ (n - 1))) → Fin 3) → (Fin (n - 1) → Bool))
    (hg : Function.Injective g) :
    let m := Nat.log 3 (2 ^ (n - 1))
    let IaccSE := accessibleInformation (keyEnsemble (n := n) g)
    let IaccXYE := accessibleInformation (lockEnsemble m)
    let IaccSPrefixE := accessibleInformation (withRegister (fun s => s.1) (keyEnsemble (n := n) g))
    let IaccXYYE := accessibleInformation (withRegister (fun v => v.2) (lockEnsemble m))
    let HY := shannon (yMarginal m)
    -- (1)–(3): Eq. (9) and Lemma 2
    IaccSE = IaccXYE ∧
    IaccSE ≤ (2 / 3 : ℝ) ^ ((m : ℝ) / 2) ∧
    IaccSE ≤ Real.exp (-(((n : ℝ) - 2) / 8)) ∧
    -- (4): §VI (ii), the measurement given the first n − 1 bits
    (∀ s' : Fin (n - 1) → Bool, (∃ x, 0 < (keyEnsemble (n := n) g).prob (s', x)) →
      ∃ M : Bool → Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ, IsPOVM M ∧
        ∀ x x' : Bool, effectProb (M x') ((keyEnsemble (n := n) g).state (s', x)) =
          if x' = x then 1 else 0) ∧
    -- (5): §VI (ii), corrected value
    IaccSPrefixE = shannon (keyEnsemble (n := n) g).prob ∧
    shannon (keyEnsemble (n := n) g).prob = 1 + m * Real.logb 2 3 ∧
    -- (6): §III closing
    IaccXYYE = shannon (lockEnsemble m).prob ∧
    shannon (lockEnsemble m).prob = 1 + m * Real.logb 2 3 ∧
    -- (7): the locking gap
    HY = m * Real.logb 2 3 ∧
    HY + 1 - (2 / 3 : ℝ) ^ ((m : ℝ) / 2) ≤ IaccXYYE - IaccXYE ∧
    IaccXYYE - IaccXYE ≤ HY + 1 ∧
    HY < IaccXYYE - IaccXYE ∧
    HY + 1 - (2 / 3 : ℝ) ^ ((m : ℝ) / 2) ≤ IaccSPrefixE - IaccSE ∧
    IaccSPrefixE - IaccSE ≤ HY + 1 ∧
    HY < IaccSPrefixE - IaccSE := by sorry

end LockingAccInfo
