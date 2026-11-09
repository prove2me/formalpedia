-- Prove2me | Theorems.Thm_OracleStateHSP_fracOracle_unitary_prepares
-- name    : OracleStateHSP.fracOracle_unitary_prepares
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:11.884503+00:00
-- url     : https://prove2.me/theorems/571b8b2a-7b45-4474-892b-a2227573a427
-- title:
--   Eq. (56): $O^\varepsilon_f$ and $U_\varphi = O^\varepsilon_f W$ are unitary, $U_\varphi|0\rangle = |\varphi^\varepsilon_f\rangle$, $U_\varphi$ is real
-- statement:
--   Let $\varepsilon \in (0, 1]$, $r, m \ge 0$ and $f : \mathbb Z_2^m \to \mathbb Z_2^m$. Then
--
--   1. the fractional oracle $O^\varepsilon_f$ of (56) is unitary;
--   2. $U_\varphi = O^\varepsilon_f W$ is unitary;
--   3. $W|0\rangle = |0\rangle|u_G\rangle$: the Hadamard gates on the group register produce $|u_G\rangle$ with the flag and answer registers zero;
--   4. $U_\varphi |0\rangle = O^\varepsilon_f W|0\rangle = |\varphi^\varepsilon_f\rangle$;
--   5. every entry of $U_\varphi$ is real, so $U_\varphi^* = U_\varphi$ and $U_\varphi^T = U_\varphi^\dagger$.
--
--   Clause 1 is what makes $O^\varepsilon_f$ a valid oracle; clause 5 is why conjugate and transpose queries give no extra power on this family.
--
--   Differences from the source:
--   - generalization: f a Simon function with nonzero period → every f : Z_2^m → Z_2^m; reason: the unitarity of O_f̃ (a self-inverse permutation), the preparation and the reality do not use the Simon property; the source's case is a special case
--   - encoding: G = Z_2^n with n = r + m → the product (Fin r → ZMod 2) × (Fin m → ZMod 2); reason: Z_2^n ≅ Z_2^r ⊕ Z_2^m as groups; the paper writes G = K ⊕ V itself
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (56) and the surrounding text, p.39; p.40 ("Uφ is real for every instance in this family")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OracleStateHSP_flagZero
import Definitions.Def_OracleStateHSP_phiEps
import Definitions.Def_OracleStateHSP_fracU

namespace OracleStateHSP

open QAlgorithms

/-- Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (56) and the sentences around it, p.39, and "`U_φ` is real for every instance in
this family", p.40: for `ε ∈ (0, 1]`,

1. the fractional oracle `O^ε_f` is unitary ("Its unitarity follows from the fact that `O_f` is a
   self-inverse unitary");
2. `U_φ = O^ε_f W` is unitary;
3. `W |0⟩ = |0⟩|u_G⟩` ("`W` applies Hadamard gates to the group register, producing `|u_G⟩` with
   the flag and answer registers set to zero");
4. `U_φ |0⟩ = O^ε_f W |0⟩ = |φ^ε_f⟩`;
5. every entry of `U_φ` is real (so `U_φ^* = U_φ` and `U_φ^T = U_φ^†`).

**Formalization Note.** Stated for every `f : Z_2^m → Z_2^m`, not only Simon functions. -/
theorem fracOracle_unitary_prepares (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (r m : ℕ)
    (f : V m → V m) :
    fracOracle ε r f ∈ Matrix.unitaryGroup (FlagQ r m) ℂ ∧
    fracU ε r f ∈ Matrix.unitaryGroup (FlagQ r m) ℂ ∧
    act (hadamardW r m) (ket (flagZero r m)) =
      (WithLp.toLp 2 fun p => if p.1 = 0 then uG r m p.2 else 0 : EuclideanSpace ℂ (FlagQ r m)) ∧
    act (fracU ε r f) (ket (flagZero r m)) = phiEps ε r f ∧
    ∀ p q, (fracU ε r f p q).im = 0 := by sorry

end OracleStateHSP
